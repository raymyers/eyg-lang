import Eyg.Types.Scheme
import Eyg.Ir.Tree

/-!
# Declarative typing judgment — pure monomorphic core (Milestone T3a)

`HasType Γ e τ ε` — "in context `Γ`, term `e` has type `τ` and may perform
effects in row `ε`". This is the **declarative** judgment (a relation), with
rules transcribed from `contextual.do_infer`; we prove the dynamics sound against
it (we do *not* prove algorithm-J itself sound — that is the T8 stretch).

The signature carries the effect row `ε` **from the start** (plan rule 1: fix all
judgment signatures once). This slice pins nothing structurally, but the pure
fragment's terms perform no effects, so they are typeable at *any* ambient `ε`
(values are pure; `ε` is an upper bound) — exactly `do_infer`'s "pass `eff`
through" for literals/variables/lambda. The T3 soundness statement instantiates
`ε := empty`; T5 un-pins it with `Perform`/`Handle`.

## Rules in this slice (pure core)

`Variable` (instantiate a context scheme), `Lambda` (arrow carrying the body's
effect row in its middle slot; the closure value itself pure), `Apply` (effect
threading — the function's latent effect equals the ambient row, per
`do_infer`'s `unify(test_eff, eff)`), monomorphic `Let`, the `Integer`/`String`/
`Binary` literals, `Builtin` (instantiate a `Builtins.scheme`), and the
**`TyEquiv` conversion rule** so row order never blocks a derivation.

Structured-data nodes (`Extend`/`Select`/`Tag`/`Case`/`Cons`/…) join in T4 and
effects (`Perform`/`Handle`) in T5 — as *new constructors*, never re-typing this
judgment.
-/

namespace Eyg.Types

open Eyg.Ir

/-- Typing context: a list of `(name, scheme)` bindings, innermost first
(`contextual` threads `[#(x, scheme), ..env]`; lookup takes the first match,
matching the interpreter's `Env` shadowing). -/
abbrev Ctx := List (String × Scheme)

/-- **Context below level `n`**: every ambient free variable of every binding's scheme is `< n`. The
side-invariant the `let_poly` rule stores and `hasType_subst`'s `let_poly` arm threads, kept off the
preservation engines (see `progress/2026-06-18-T6-let_poly-levelmap-mono-and-wfbelow-decision.md`).
Defined here (before `HasType`) so the `let_poly` constructor can carry it. -/
def CtxWf (n : Nat) (Γ : Ctx) : Prop := ∀ b ∈ Γ, ∀ i ∈ Scheme.freeVars b.2, i < n

/-- **Context below level `ℓ`** (level-native): every level occurring in every binding's scheme body
(quantifier level *and* ambient references alike, via `Ty.levels`) is `< ℓ`. The side-invariant the
level-native `let_poly` rule stores and `hasType_subst`'s `let_poly` arm threads. -/
def CtxWfV (ℓ : Nat) (Γ : Ctx) : Prop := ∀ b ∈ Γ, ∀ l ∈ b.2.body.levels, l < ℓ

namespace Ty

/-- **`TyEquiv` preserves the level set** (level-native analog of `freeVars_tyEquiv`; row/effect
reorderings permute leaves but keep the multiset, hence the set, of level tags). -/
theorem levels_tyEquiv {s t : Ty} (h : TyEquiv s t) : ∀ l, l ∈ levels s ↔ l ∈ levels t := by
  induction h with
  | refl => intro l; exact Iff.rfl
  | symm _ ih => intro l; exact (ih l).symm
  | trans _ _ ih1 ih2 => intro l; exact (ih1 l).trans (ih2 l)
  | congrFun _ _ _ iha ihe ihr =>
      intro l; simp only [levels, List.mem_append]; rw [iha l, ihe l, ihr l]
  | congrList _ ih => intro l; simp only [levels]; exact ih l
  | congrRecord _ ih => intro l; simp only [levels]; exact ih l
  | congrUnion _ ih => intro l; simp only [levels]; exact ih l
  | congrPromise _ ih => intro l; simp only [levels]; exact ih l
  | congrRow _ _ ihf iht =>
      intro l; simp only [levels, List.mem_append]; rw [ihf l, iht l]
  | congrEff _ _ _ iha ihb iht =>
      intro l; simp only [levels, List.mem_append]; rw [iha l, ihb l, iht l]
  | swapRow _ => intro l; simp only [levels, List.mem_append]; tauto
  | swapEff _ => intro l; simp only [levels, List.mem_append]; tauto

end Ty

/-! ## `Handle` scheme component types (T5)

The deep-handler scheme `handle(l)` (`contextual.gleam` `handle`) factors into these
pieces. They are `abbrev`s (reducible) so `canonical_arrow` / `tyEquiv_fun_inv` see the
arrows through them. -/

/-- The resumption type `Fun(reply, tail, ret)` — a delimited continuation. -/
abbrev kontTy (reply tail ret : Ty) : Ty := .fun reply tail ret
/-- The handler type `Fun(lift, ∅, Fun(kont, tail, ret))` — gets the performed value
and the resumption, returns the answer under the discharged row `tail`. -/
abbrev handlerTy (lift reply tail ret : Ty) : Ty :=
  .fun lift .empty (.fun (kontTy reply tail ret) tail ret)
/-- The guarded-computation type `Fun({}, ⟨l:(lift,reply)|tail⟩, ret)` — runs under
the handled row; `l` is discharged by the handler. -/
abbrev execTy (l : String) (lift reply tail ret : Ty) : Ty :=
  .fun (.record .empty) (.effectExtend l lift reply tail) ret
/-- `handle(l) = Fun(handler, ∅, Fun(exec, tail, ret))`. -/
abbrev handleTy (l : String) (lift reply tail ret : Ty) : Ty :=
  .fun (handlerTy lift reply tail ret) .empty
    (.fun (execTy l lift reply tail ret) tail ret)

/-- The declarative typing judgment for EYG terms, **level-parameterized** (G1 Caveat 5). The extra
`Nat` index `lvl` is the ambient de-Bruijn *level*: `let_poly` generalizes at *exactly* `lvl` via the
level-native `Scheme.genAtV`/`CtxWfV` (so nested generalization layers are structurally distinguished
by their level tag), types its body at `lvl + 1`, and carries **no `noLambdaLet`** — nested
`Let`-binds-`Lambda` terms are genuinely accepted. `lam`/`let_` descend to a stored fresh sublevel
`lvl'`; `var`/`builtin` instantiate via the level-native `Scheme.instantiateV`. -/
inductive HasType {m : Type} : Nat → Ctx → Tree.Node m → Ty → Ty → Prop where
  /-- Variable: look up a scheme and instantiate it (level-natively). -/
  | var {lvl Γ x s args ε a} :
      Γ.lookup x = some s →
      HasType lvl Γ ⟨.Variable x, a⟩ (s.instantiateV args) ε
  /-- Lambda: descend under the mono binding at a stored sublevel `lvl' ≥ lvl` covering `argTy`'s
  level tags. The arrow carries the body's effect row `εb`; the closure value is pure. -/
  | lam {lvl lvl' Γ x body argTy εb retTy ε a} :
      lvl ≤ lvl' →
      (∀ l ∈ argTy.levels, l < lvl') →
      HasType lvl' ((x, .mono argTy) :: Γ) body retTy εb →
      HasType lvl Γ ⟨.Lambda x body, a⟩ (.fun argTy εb retTy) ε
  /-- Application: the function's latent effect `εf` may be weakened to the ambient row `ε`. -/
  | app {lvl Γ f arg argTy εf retTy ε a} :
      HasType lvl Γ f (.fun argTy εf retTy) ε →
      Ty.EffWeaken εf ε →
      HasType lvl Γ arg argTy ε →
      HasType lvl Γ ⟨.Apply f arg, a⟩ retTy ε
  /-- Monomorphic `let`: like `lam`, descend under the mono binding at a stored sublevel. -/
  | let_ {lvl lvl' Γ x defn body defnTy bodyTy ε a} :
      HasType lvl Γ defn defnTy ε →
      lvl ≤ lvl' →
      (∀ l ∈ defnTy.levels, l < lvl') →
      HasType lvl' ((x, .mono defnTy) :: Γ) body bodyTy ε →
      HasType lvl Γ ⟨.Let x defn body, a⟩ bodyTy ε
  /-- **Polymorphic `let`** (value-restricted), generalizing at **exactly** `lvl` via
  `Scheme.genAtV lvl`, recording `CtxWfV lvl Γ`, typing its body at `lvl + 1`. **No `noLambdaLet`** —
  nested `Let`-binds-`Lambda` bodies (the Caveat-5 shape) are accepted. -/
  | let_poly {lvl Γ x lx lbody la body defnTy bodyTy ε a} :
      HasType lvl Γ ⟨.Lambda lx lbody, la⟩ defnTy ε →
      CtxWfV lvl Γ →
      HasType (lvl + 1) ((x, Scheme.genAtV lvl defnTy) :: Γ) body bodyTy ε →
      HasType lvl Γ ⟨.Let x ⟨.Lambda lx lbody, la⟩ body, a⟩ bodyTy ε
  /-- Integer literal. -/
  | int {lvl Γ n ε a} : HasType lvl Γ ⟨.Integer n, a⟩ .integer ε
  /-- String literal. -/
  | str {lvl Γ s ε a} : HasType lvl Γ ⟨.String s, a⟩ .string ε
  /-- Binary literal. -/
  | bin {lvl Γ b ε a} : HasType lvl Γ ⟨.Binary b, a⟩ .binary ε
  /-- Builtin: instantiate its scheme level-natively. -/
  | builtin {lvl Γ id s args ε a} :
      Builtins.scheme id = some s →
      HasType lvl Γ ⟨.Builtin id, a⟩ (s.instantiateV args) ε
  /-- The empty list `Tail`, polymorphic in its element type. -/
  | tail {lvl Γ elem ε a} : HasType lvl Γ ⟨.Tail, a⟩ (.list elem) ε
  /-- List `Cons`: `∀α. α → List α → List α`. -/
  | cons {lvl Γ elem ε a} :
      HasType lvl Γ ⟨.Cons, a⟩ (.fun elem .empty (.fun (.list elem) .empty (.list elem))) ε
  /-- Variant injection `Tag l`: `∀α r. α → ⟨l : α | r⟩`. -/
  | tag {lvl Γ l elem tail ε a} :
      HasType lvl Γ ⟨.Tag l, a⟩ (.fun elem .empty (.union (.rowExtend l elem tail))) ε
  /-- The empty-variant eliminator `NoCases`: `∀β. ⟨⟩ → β`. -/
  | nocases {lvl Γ ret ε a} :
      HasType lvl Γ ⟨.NoCases, a⟩ (.fun (.union .empty) .empty ret) ε
  /-- Variant decomposition `Case l`. -/
  | case_ {lvl Γ l inner eff ret tail ε a} :
      HasType lvl Γ ⟨.Case l, a⟩
        (.fun (.fun inner eff ret) .empty
          (.fun (.fun (.union tail) eff ret) .empty
            (.fun (.union (.rowExtend l inner tail)) eff ret))) ε
  /-- Record projection `Select l`: `∀α r. {l:α|r} → α`. -/
  | select {lvl Γ l fieldTy tail ε a} :
      HasType lvl Γ ⟨.Select l, a⟩ (.fun (.record (.rowExtend l fieldTy tail)) .empty fieldTy) ε
  /-- Record extension `Extend l`: `∀α r. α → {r} → {l:α|r}`. -/
  | extend {lvl Γ l fieldTy row ε a} :
      HasType lvl Γ ⟨.Extend l, a⟩ (.fun fieldTy .empty
        (.fun (.record row) .empty (.record (.rowExtend l fieldTy row)))) ε
  /-- Record overwrite `Overwrite l`: `∀α β r. α → {l:β|r} → {l:α|r}`. -/
  | overwrite {lvl Γ l newTy oldTy tail ε a} :
      HasType lvl Γ ⟨.Overwrite l, a⟩ (.fun newTy .empty
        (.fun (.record (.rowExtend l oldTy tail)) .empty
          (.record (.rowExtend l newTy tail)))) ε
  /-- The empty record `Empty`. -/
  | empty {lvl Γ ε a} : HasType lvl Γ ⟨.Empty, a⟩ (.record .empty) ε
  /-- Effect operation `Perform l`: `∀α β μ. α →⟨l:(α,β)|μ⟩ β`. -/
  | perform {lvl Γ l a b μ ε ann} :
      HasType lvl Γ ⟨.Perform l, ann⟩ (.fun a (.effectExtend l a b μ) b) ε
  /-- Deep handler `Handle l`. -/
  | handle {lvl Γ l lift reply tail ret ε ann} :
      HasType lvl Γ ⟨.Handle l, ann⟩ (handleTy l lift reply tail ret) ε
  /-- **Conversion**: types and effect rows may be replaced by `TyEquiv`-equal ones. -/
  | conv {lvl Γ e τ τ' ε ε'} :
      HasType lvl Γ e τ ε → Ty.TyEquiv τ τ' → Ty.TyEquiv ε ε' →
      HasType lvl Γ e τ' ε'

/-! ## Level-native context substitution `substCtxAt` and the `PolyAbove` invariant -/

/-- Apply a level-`ℓ` type substitution to every scheme in a typing context. -/
def substCtxAt (ℓ : Nat) (σ : Nat → Ty) (Γ : Ctx) : Ctx :=
  Γ.map (fun b => (b.1, Scheme.substSchemeVAt ℓ σ b.2))

@[simp] theorem substCtxAt_nil (ℓ : Nat) (σ : Nat → Ty) : substCtxAt ℓ σ [] = [] := rfl

@[simp] theorem substCtxAt_cons (ℓ : Nat) (σ : Nat → Ty) (x : String) (s : Scheme) (Γ : Ctx) :
    substCtxAt ℓ σ ((x, s) :: Γ) = (x, Scheme.substSchemeVAt ℓ σ s) :: substCtxAt ℓ σ Γ := rfl

/-- Context lookup commutes with `substCtxAt` (keys preserved). -/
theorem substCtxAt_lookup {ℓ : Nat} {σ : Nat → Ty} {Γ : Ctx} {x : String} {s : Scheme}
    (h : Γ.lookup x = some s) :
    (substCtxAt ℓ σ Γ).lookup x = some (Scheme.substSchemeVAt ℓ σ s) := by
  induction Γ with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
      obtain ⟨y, sy⟩ := hd
      simp only [substCtxAt_cons, List.lookup_cons] at h ⊢
      by_cases hxy : (x == y) = true
      · simp only [hxy] at h ⊢; cases h; rfl
      · simp only [hxy] at h ⊢; exact ih h

/-- Membership recovery from a successful lookup. -/
theorem lookup_mem {Γ : Ctx} {x : String} {s : Scheme} (h : Γ.lookup x = some s) : (x, s) ∈ Γ := by
  induction Γ with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
      obtain ⟨y, sy⟩ := hd
      simp only [List.lookup_cons] at h
      by_cases hxy : (x == y) = true
      · simp only [hxy] at h; cases h
        have : x = y := by simpa using hxy
        subst this; exact List.mem_cons_self
      · simp only [hxy] at h; exact List.mem_cons_of_mem _ (ih h)

/-- **`substCtxAt` fixes a context below the substitution level.** -/
theorem substCtxAt_fix {ℓ : Nat} {σ : Nat → Ty} {Γ : Ctx} (hΓ : CtxWfV ℓ Γ) :
    substCtxAt ℓ σ Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨y, s⟩ := hd
      have hbody : Ty.substAt ℓ σ s.body = s.body := by
        apply Ty.substAt_eq_self_of_not_mem
        intro i hi
        exact absurd (hΓ (y, s) (by simp) ℓ (Ty.mem_levels_of_mem_freeVarsAt hi)) (lt_irrefl ℓ)
      have htl : CtxWfV ℓ tl := fun b hb => hΓ b (List.mem_cons_of_mem _ hb)
      simp only [substCtxAt_cons, ih htl]
      exact congrArg (fun z => (y, z) :: tl) (Scheme.ext' rfl rfl hbody)

/-- **`CtxWfV` is stable under a level-`ℓ` substitution** (`ℓ < L`, `σ`'s levels `≤ ℓ`). -/
theorem ctxWfV_substCtxAt {ℓ L : Nat} {σ : Nat → Ty} (hlt : ℓ < L)
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l ≤ ℓ) {Γ : Ctx} (hΓ : CtxWfV L Γ) :
    CtxWfV L (substCtxAt ℓ σ Γ) := by
  intro b hb l hl
  simp only [substCtxAt, List.mem_map] at hb
  obtain ⟨⟨y, s⟩, hmem, rfl⟩ := hb
  simp only [Scheme.substSchemeVAt] at hl
  rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
  · exact hΓ (y, s) hmem l hl'
  · exact Nat.lt_of_le_of_lt (hσ i l hi) hlt

/-- **The `let_poly` context rewrite.** -/
theorem substCtxAt_cons_genAtV {ℓ k : Nat} (hne : ℓ ≠ k) {σ : Nat → Ty}
    (hclean : ∀ i, k ∉ (σ i).levels) (x : String) (d : Ty) (Γ : Ctx) :
    substCtxAt ℓ σ ((x, Scheme.genAtV k d) :: Γ)
      = (x, Scheme.genAtV k (Ty.substAt ℓ σ d)) :: substCtxAt ℓ σ Γ := by
  simp only [substCtxAt_cons, substSchemeVAt_genAtV hne hclean]

/-- **Context invariant for the `substAt ℓ` re-typing induction.** Every polymorphic (`arity ≠ 0`)
binding sits at a level strictly above the opening level `ℓ`. Mono bindings are unconstrained. -/
def PolyAbove (ℓ : Nat) (Γ : Ctx) : Prop := ∀ b ∈ Γ, b.2.arity = 0 ∨ ℓ < b.2.level

theorem polyAbove_cons_mono {ℓ : Nat} {x : String} {t : Ty} {Γ : Ctx}
    (hΓ : PolyAbove ℓ Γ) : PolyAbove ℓ ((x, Scheme.mono t) :: Γ) := by
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact Or.inl rfl
  · exact hΓ b hb

/-! ## Level-native type substitution — the instantiation-direction re-typing lemma -/

/-- **Instantiation-direction type substitution for `HasType`.** A derivation re-types under an
**outer** level-`ℓ` substitution `substAt ℓ σ` (`ℓ ≠ 0`, `ℓ < lvl`, `σ`'s levels `≤ ℓ`, context
polymorphic bindings above `ℓ`). The `let_poly` arm reconstructs via `substCtxAt_cons_genAtV`
(level-native, no `LevelMap`); fires non-vacuously for arbitrarily deep nesting. -/
theorem hasType_subst {ℓ : Nat} (hℓ : ℓ ≠ 0) (σ : Nat → Ty)
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l ≤ ℓ)
    {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    (h : HasType lvl Γ e τ ε) (hlt : ℓ < lvl) (hΓ : PolyAbove ℓ Γ) :
    HasType lvl (substCtxAt ℓ σ Γ) e (Ty.substAt ℓ σ τ) (Ty.substAt ℓ σ ε) := by
  revert hlt hΓ
  induction h with
  | @var lvl Γ x s args ε a hl =>
      intro hlt hΓ
      have hdisj : s.arity = 0 ∨ (ℓ ≠ s.level ∧ ∀ i, ∀ j, j ∉ Ty.freeVarsAt s.level (σ i)) := by
        by_cases h0 : s.arity = 0
        · exact Or.inl h0
        · have hlvl : ℓ < s.level := (hΓ (x, s) (lookup_mem hl)).resolve_left h0
          exact Or.inr ⟨Nat.ne_of_lt hlvl,
            Ty.clean_of_levels_lt (fun i l hl' => Nat.lt_succ_of_le (hσ i l hl')) hlvl⟩
      rw [substAt_instantiateV_scheme hdisj args]
      exact HasType.var (substCtxAt_lookup hl)
  | @builtin lvl Γ id s args ε a hs =>
      intro hlt hΓ
      rw [substAt_instantiateV_closed (by rw [Builtins.scheme_level hs]; exact hℓ)
            (Builtins.scheme_no_level hℓ hs) args,
          Builtins.scheme_substSchemeVAt hℓ σ hs]
      exact HasType.builtin hs
  | @lam lvl lvl' Γ x body argTy εb retTy ε a hle hfv hbody ih =>
      intro hlt hΓ
      simp only [Ty.substAt]
      refine HasType.lam hle ?_ ?_
      · intro l hl
        rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
        · exact hfv l hl'
        · exact Nat.lt_of_le_of_lt (hσ i l hi) (Nat.lt_of_lt_of_le hlt hle)
      · have hb := ih (Nat.lt_of_lt_of_le hlt hle) (polyAbove_cons_mono hΓ)
        rw [substCtxAt_cons, substSchemeVAt_mono] at hb
        exact hb
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg ihf iharg =>
      intro hlt hΓ
      have hf' := ihf hlt hΓ
      simp only [Ty.substAt] at hf'
      exact HasType.app hf' (Ty.substAt_effWeaken ℓ σ hw) (iharg hlt hΓ)
  | @let_ lvl lvl' Γ x defn body defnTy bodyTy ε a hdefn hle hfv hbody ihdefn ihbody =>
      intro hlt hΓ
      have hb := ihbody (Nat.lt_of_lt_of_le hlt hle) (polyAbove_cons_mono hΓ)
      rw [substCtxAt_cons, substSchemeVAt_mono] at hb
      refine HasType.let_ (ihdefn hlt hΓ) hle ?_ hb
      intro l hl
      rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
      · exact hfv l hl'
      · exact Nat.lt_of_le_of_lt (hσ i l hi) (Nat.lt_of_lt_of_le hlt hle)
  | @let_poly lvl Γ x lx lbody la body defnTy bodyTy ε a hdefn hcw hbody ihdefn ihbody =>
      intro hlt hΓ
      have hne : ℓ ≠ lvl := Nat.ne_of_lt hlt
      have hcleanlvl : ∀ i, lvl ∉ (σ i).levels := fun i hmem => absurd (hσ i lvl hmem) (by omega)
      have hdefn' := ihdefn hlt hΓ
      have hΓ1 : PolyAbove ℓ ((x, Scheme.genAtV lvl defnTy) :: Γ) := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · by_cases h0 : (Scheme.genAtV lvl defnTy).arity = 0
          · exact Or.inl h0
          · exact Or.inr (by simp only [Scheme.genAtV]; exact hlt)
        · exact hΓ b hb
      have hbodyIH := ihbody (by omega : ℓ < lvl + 1) hΓ1
      rw [substCtxAt_cons_genAtV hne hcleanlvl] at hbodyIH
      exact HasType.let_poly hdefn' (ctxWfV_substCtxAt hlt hσ hcw) hbodyIH
  | int => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.int
  | str => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.str
  | bin => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.bin
  | tail => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.tail
  | cons => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.cons
  | tag => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.tag
  | nocases => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.nocases
  | case_ => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.case_
  | select => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.select
  | extend => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.extend
  | overwrite => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.overwrite
  | empty => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.empty
  | perform => intro hlt hΓ; simp only [Ty.substAt]; exact HasType.perform
  | @handle lvl Γ l lift reply tail ret ε a =>
      intro hlt hΓ
      have heq : Ty.substAt ℓ σ (handleTy l lift reply tail ret)
          = handleTy l (Ty.substAt ℓ σ lift) (Ty.substAt ℓ σ reply) (Ty.substAt ℓ σ tail)
              (Ty.substAt ℓ σ ret) := by
        simp [handleTy, handlerTy, execTy, kontTy, Ty.substAt]
      rw [heq]; exact HasType.handle
  | conv _ hτ hε ih =>
      intro hlt hΓ
      exact HasType.conv (ih hlt hΓ) (Ty.substAt_tyEquiv ℓ σ hτ) (Ty.substAt_tyEquiv ℓ σ hε)

/-! ## The level-native readiness keystone (term level) -/

/-- **The instantiation keystone for a let-bound lambda (level-native).** For a lambda typed at
ambient level `ℓ` via its `lam` components — body at a strictly higher level `lvl' > ℓ`, context `Γ`
below `ℓ`, instantiation args with levels `≤ ℓ` — **every** instantiation of the generalized scheme
`genAtV ℓ (.fun argTy εb retTy)` is a genuine `substAt ℓ` re-typing of the lambda's own derivation,
with no `noLambdaLet` restriction. -/
theorem genAtV_instantiate_lam_ready {ℓ : Nat} (hℓ : ℓ ≠ 0)
    {lvl' : Nat} {Γ : Ctx} {x : String} {lbody : Tree.Node m} {la : m}
    {argTy εb retTy ε : Ty}
    (hlt : ℓ < lvl')
    (hfv : ∀ l ∈ argTy.levels, l < lvl')
    (hbody : HasType lvl' ((x, .mono argTy) :: Γ) lbody retTy εb)
    (hΓpa : PolyAbove ℓ Γ)
    (hΓwf : CtxWfV ℓ Γ)
    (args : List Ty)
    (hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l ≤ ℓ) :
    HasType ℓ Γ ⟨.Lambda x lbody, la⟩
      ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) ε := by
  set defnTy : Ty := .fun argTy εb retTy with hdefn
  have hΓpa' : PolyAbove ℓ ((x, Scheme.mono argTy) :: Γ) := polyAbove_cons_mono hΓpa
  by_cases h0 : (Scheme.genAtV ℓ defnTy).arity = 0
  · rw [Scheme.instantiateV, if_pos h0, ← Ty.substAt_var_self ℓ defnTy]
    have hσ : ∀ i, ∀ l ∈ ((fun i => Ty.var ℓ i) i).levels, l ≤ ℓ := by
      intro i l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega
    have hb := hasType_subst hℓ (fun i => Ty.var ℓ i) hσ hbody hlt hΓpa'
    rw [substCtxAt_cons, substSchemeVAt_mono] at hb
    have hlam := HasType.lam (a := la) (ε := ε) (le_of_lt hlt)
      (by intro l hl
          rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
          · exact hfv l hl'
          · simp only [Ty.levels, List.mem_singleton] at hi; omega) hb
    have hfix : substCtxAt ℓ (fun i => Ty.var ℓ i) Γ = Γ := substCtxAt_fix hΓwf
    rw [hfix] at hlam
    simpa only [Ty.substAt, hdefn] using hlam
  · rw [Scheme.instantiateV, if_neg h0]
    have hσ : ∀ i, ∀ l ∈ (args.getD i (.var ℓ i)).levels, l ≤ ℓ := by
      intro i l hl
      rcases lt_or_ge i args.length with hi | hi
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hl
        exact hargs _ (List.getElem_mem hi) l hl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none] at hl
        simp only [Ty.levels, List.mem_singleton] at hl; omega
    have hb := hasType_subst hℓ (fun i => args.getD i (.var ℓ i)) hσ hbody hlt hΓpa'
    rw [substCtxAt_cons, substSchemeVAt_mono] at hb
    have hlam := HasType.lam (a := la) (ε := ε) (le_of_lt hlt)
      (by intro l hl
          rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
          · exact hfv l hl'
          · exact Nat.lt_of_le_of_lt (hσ i l hi) hlt) hb
    have hfix : substCtxAt ℓ (fun i => args.getD i (.var ℓ i)) Γ = Γ := substCtxAt_fix hΓwf
    rw [hfix] at hlam
    simpa only [Ty.substAt, hdefn] using hlam

/-! ## Context-binding conversion -/

/-- **`CtxWfV` survives a `TyEquiv` context-binding rewrite** (level-native; `TyEquiv` preserves the
level set via `Ty.levels_tyEquiv`). -/
theorem ctxWfV_ctxConv {n : Nat} {Δ Γ : Ctx} {x : String} {σ σ' : Ty}
    (hc : Ty.TyEquiv σ' σ) (h : CtxWfV n (Δ ++ (x, .mono σ) :: Γ)) :
    CtxWfV n (Δ ++ (x, .mono σ') :: Γ) := by
  intro b hb i hi
  rcases List.mem_append.mp hb with hbΔ | hbcons
  · exact h b (List.mem_append.mpr (Or.inl hbΔ)) i hi
  · rcases List.mem_cons.mp hbcons with rfl | hbΓ
    · simp only [Scheme.mono] at hi
      have hi' : i ∈ Ty.levels σ := (Ty.levels_tyEquiv hc i).mp hi
      have hb0 := h (x, Scheme.mono σ) (List.mem_append.mpr (Or.inr (List.mem_cons_self ..))) i
      simp only [Scheme.mono] at hb0
      exact hb0 hi'
    · exact h b (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hbΓ))) i hi

/-- **Context-binding conversion** (depth-general, level-native). Needed by `stackSeg_conv_input`. -/
theorem hasType_ctxConv {m : Type} {lvl : Nat} {Γ₀ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    (h : HasType lvl Γ₀ e τ ε) :
    ∀ (Δ Γ : Ctx) (x : String) (σ σ' : Ty),
      Γ₀ = Δ ++ (x, .mono σ) :: Γ → Ty.TyEquiv σ' σ →
      HasType lvl (Δ ++ (x, .mono σ') :: Γ) e τ ε := by
  induction h with
  | @var lvl Γ₁ y s args ε' a hl =>
      intro Δ Γ x σ σ' heq hc; subst heq
      rw [List.lookup_append] at hl
      cases hΔ : Δ.lookup y with
      | some v =>
          rw [hΔ, Option.some_or] at hl; cases hl
          exact HasType.var (by rw [List.lookup_append, hΔ, Option.some_or])
      | none =>
          rw [hΔ, Option.none_or] at hl
          by_cases hyx : (y == x) = true
          · simp only [List.lookup_cons, hyx] at hl; cases hl
            refine HasType.conv
              (HasType.var (s := .mono σ') (args := args)
                (by simp only [List.lookup_append, hΔ, Option.none_or, List.lookup_cons, hyx]))
              ?_ (.refl _)
            simp only [Scheme.instantiateV_mono]; exact hc
          · simp only [List.lookup_cons, hyx, Bool.false_eq_true] at hl ⊢
            exact HasType.var (s := s) (args := args)
              (by simp only [List.lookup_append, hΔ, Option.none_or, List.lookup_cons, hyx,
                Bool.false_eq_true]; exact hl)
  | @lam lvl lvl' Γ₁ z body argTy εb retTy ε' a hle hfv hbody ih =>
      intro Δ Γ x σ σ' heq hc; subst heq
      exact HasType.lam hle hfv (ih ((z, .mono argTy) :: Δ) Γ x σ σ' rfl hc)
  | @app lvl Γ₁ f arg argTy εf retTy ε' a hf hw harg ihf iharg =>
      intro Δ Γ x σ σ' heq hc; subst heq
      exact HasType.app (ihf Δ Γ x σ σ' rfl hc) hw (iharg Δ Γ x σ σ' rfl hc)
  | @let_ lvl lvl' Γ₁ z defn body defnTy bodyTy ε' a hdefn hle hfv hbody ihdefn ihbody =>
      intro Δ Γ x σ σ' heq hc; subst heq
      exact HasType.let_ (ihdefn Δ Γ x σ σ' rfl hc) hle hfv
        (ihbody ((z, .mono defnTy) :: Δ) Γ x σ σ' rfl hc)
  | @let_poly lvl Γ₁ z lx lbody la body defnTy bodyTy ε' a hdefn hcw hbody ihdefn ihbody =>
      intro Δ Γ x σ σ' heq hc; subst heq
      exact HasType.let_poly (ihdefn Δ Γ x σ σ' rfl hc) (ctxWfV_ctxConv hc hcw)
        (ihbody ((z, Scheme.genAtV lvl defnTy) :: Δ) Γ x σ σ' rfl hc)
  | int => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.int
  | str => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.str
  | bin => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.bin
  | builtin hs => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.builtin hs
  | tail => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.tail
  | cons => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.cons
  | tag => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.tag
  | nocases => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.nocases
  | case_ => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.case_
  | select => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.select
  | extend => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.extend
  | overwrite => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.overwrite
  | empty => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.empty
  | perform => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.perform
  | handle => intro Δ Γ x σ σ' heq hc; subst heq; exact HasType.handle
  | @conv lvl Γ₁ e' τ' τ'' ε₁ ε₂ hbody hτ hε ih =>
      intro Δ Γ x σ σ' heq hc; subst heq
      exact HasType.conv (ih Δ Γ x σ σ' rfl hc) hτ hε

/-- The head-binding specialization (`Δ = []`), the form `stackSeg_conv_input` uses. -/
theorem hasType_ctxHead_conv {m : Type} {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {x : String}
    {σ σ' τ ε : Ty} (h : HasType lvl ((x, .mono σ) :: Γ) e τ ε) (hc : Ty.TyEquiv σ' σ) :
    HasType lvl ((x, .mono σ') :: Γ) e τ ε :=
  hasType_ctxConv h [] Γ x σ σ' rfl hc

/-! ## Sanity checks -/

section Examples
open Eyg.Ir.Tree

-- `(\x. x) 1 : integer ! empty`
example : HasType (m := Unit) 0 [] (apply (lambda "x" (variable_ "x")) (integer 1))
    .integer .empty := by
  refine HasType.app (argTy := .integer) ?_ (Ty.effWeaken_refl _) ?_
  · exact HasType.lam (lvl' := 0) (le_refl _)
      (by intro l hl; simp only [Ty.levels] at hl; exact absurd hl (by simp))
      (HasType.var (s := .mono .integer) (args := []) rfl)
  · exact HasType.int

-- `\x. x` typeable at a non-empty ambient row (the closure value is pure).
example : HasType (m := Unit) 0 [] (lambda "x" (variable_ "x"))
    (.fun .integer .empty .integer) (.effectExtend "Log" .string .empty .empty) :=
  HasType.lam (lvl' := 0) (le_refl _)
    (by intro l hl; simp only [Ty.levels] at hl; exact absurd hl (by simp))
    (HasType.var (s := .mono .integer) (args := []) rfl)

end Examples

end Eyg.Types
