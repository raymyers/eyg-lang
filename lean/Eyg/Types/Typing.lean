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
  nested `Let`-binds-`Lambda` bodies (the Caveat-5 shape) are accepted. The defn lambda's structure is
  **inlined** (its body `lbody` typed at a stored sublevel `lvl'` **strictly** above `lvl`,
  `lvl < lvl'`), enforcing the Rémy/OCaml fresh-level generalization discipline: a defn whose own
  generalization would collide on `lvl` is unconstructable. The strict descent makes `NoGenAt lvl`
  of the defn hold for free (via `noGenAt_of_lt`), discharging the closure-readiness wrapper (G1
  Caveat 5). `defnTy = .fun argTy εb retTy`. -/
  | let_poly {lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a} :
      lvl < lvl' →
      (∀ l ∈ argTy.levels, l < lvl') →
      HasType lvl' ((lx, .mono argTy) :: Γ) lbody retTy εb →
      CtxWfV lvl Γ →
      HasType (lvl + 1) ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body bodyTy ε →
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

/-- **The defn-lambda derivation implicit in a `let_poly` node**, reconstructed from the inlined
strict-sublevel components (`HasType.lam` with `lvl ≤ lvl'` from `le_of_lt hstrict`). The bridge that
lets inversion sites hand a lambda-*node* derivation to the closure-readiness wrapper. -/
theorem HasType.letpoly_defn {m : Type} {lvl lvl' : Nat} {Γ : Ctx} {lx : String}
    {lbody : Tree.Node m} {la : m} {argTy εb retTy ε : Ty}
    (hstrict : lvl < lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
    (hbodydefn : HasType lvl' ((lx, .mono argTy) :: Γ) lbody retTy εb) :
    HasType lvl Γ ⟨.Lambda lx lbody, la⟩ (.fun argTy εb retTy) ε :=
  HasType.lam (le_of_lt hstrict) hfv hbodydefn

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

/-! ## Free-variable-aware substitution precondition (`PolyAboveFV`)

The blanket `PolyAbove ℓ Γ` is **false** for the ambient context of any sequential/nested `let_poly`
(an outer polymorphic binding lives at a *lower* level than the inner let's opening level `ℓ`), which
regresses basic sequential let-polymorphism. But `hasType_subst`'s `var` arm only ever consumes the
"disjoint/clean" fact for the variable **actually looked up** by the term being re-typed. So the
correct precondition is *free-variable-aware*: constrain only the bindings `e` references, not every
binding in `Γ`. Every binder the induction descends under adds a binding that is automatically "fine"
(a `mono` scheme has `arity = 0`; a `let_poly`'s `genAtV lvl` scheme sits at `level = lvl > ℓ`), so
the invariant threads without ever demanding anything of the pre-existing ambient bindings that `e`
does not touch. -/

/-- **Free variables of a term**: the variable names it looks up in the ambient context, with each
binder removing its bound name. Only the four node shapes carrying sub-terms recurse; every atomic
former has no free variables. -/
def _root_.Eyg.Ir.Tree.Node.freeVars {m : Type} : Tree.Node m → List String
  | ⟨.Variable x, _⟩ => [x]
  | ⟨.Lambda x body, _⟩ => body.freeVars.filter (· != x)
  | ⟨.Apply f arg, _⟩ => f.freeVars ++ arg.freeVars
  | ⟨.Let x defn body, _⟩ => defn.freeVars ++ body.freeVars.filter (· != x)
  | ⟨_, _⟩ => []

/-- **Free-variable-aware context invariant** for the `substAt ℓ` re-typing induction: every binding
`e` actually references (via a free variable resolved in `Γ`) is either monomorphic (`arity = 0`) or
sits at a level strictly above the opening level `ℓ`. Strictly weaker than blanket `PolyAbove ℓ Γ`
(which quantifies over *all* of `Γ`), and — unlike it — holds for the ambient context of a
sequential/nested `let_poly` whenever the generalized body does not reference the lower-level outer
binding. -/
def PolyAboveFV {m : Type} (ℓ : Nat) (Γ : Ctx) (e : Tree.Node m) : Prop :=
  ∀ x ∈ e.freeVars, ∀ s, Γ.lookup x = some s → s.arity = 0 ∨ (s.level ≠ 0 ∧ s.level ≠ ℓ)

/-- Blanket `PolyAbove` implies the free-variable-aware form for every term. -/
theorem polyAboveFV_of_polyAbove {m : Type} {ℓ : Nat} {Γ : Ctx} {e : Tree.Node m}
    (hΓ : PolyAbove ℓ Γ) : PolyAboveFV ℓ Γ e := by
  intro x _ s hlk
  rcases hΓ (x, s) (lookup_mem hlk) with h | h
  · exact Or.inl h
  · have h' : ℓ < s.level := h
    exact Or.inr ⟨by omega, by omega⟩

/-- Restrict the precondition to a sub-term whose free variables are all free in the whole term.
`hΓ` precedes `hmem` so that the enclosing term `e` is pinned (from `hΓ`) before the membership
obligation elaborates — letting `e.freeVars` reduce definitionally. -/
theorem polyAboveFV_sub {m : Type} {ℓ : Nat} {Γ : Ctx} {e sub : Tree.Node m}
    (hΓ : PolyAboveFV ℓ Γ e) (hmem : ∀ y ∈ sub.freeVars, y ∈ e.freeVars) :
    PolyAboveFV ℓ Γ sub :=
  fun y hy s hlk => hΓ y (hmem y hy) s hlk

/-- Descend under a *fine* binding `(x, s0)` (`s0.arity = 0` or `ℓ < s0.level`): a free variable of
the sub-term other than `x` remains free in the enclosing term (so the precondition transports), and
`x` itself resolves to the fine binding. `hΓ` precedes `hmem` (see `polyAboveFV_sub`). -/
theorem polyAboveFV_bind {m : Type} {ℓ : Nat} {Γ : Ctx} {x : String} {s0 : Scheme}
    {e sub : Tree.Node m} (hs0 : s0.arity = 0 ∨ (s0.level ≠ 0 ∧ s0.level ≠ ℓ))
    (hΓ : PolyAboveFV ℓ Γ e)
    (hmem : ∀ y ∈ sub.freeVars, y ≠ x → y ∈ e.freeVars) :
    PolyAboveFV ℓ ((x, s0) :: Γ) sub := by
  intro y hy s hlk
  rw [List.lookup_cons] at hlk
  by_cases hyx : (y == x) = true
  · simp only [hyx] at hlk; cases hlk; exact hs0
  · simp only [hyx] at hlk
    have hne : y ≠ x := by intro h; subst h; exact hyx (by simp)
    exact hΓ y (hmem y hy hne) s hlk

/-! ## Runtime nonzero-poly-level context invariant (`CtxPolyBd`)

The blocker for the `let_poly` preservation case: `genAtV_closure_ready_value_node` needs
`PolyAboveFV lvl Γ (defn lambda)` and `lvl ≠ 0`, and `CtxWfV lvl Γ` alone cannot supply the
`s.level ≠ 0` half of `PolyAboveFV`'s poly disjunct (a `genAtV 0 d` binding with `0 ∈ d.levels`
satisfies `CtxWfV` yet has level `0`). The fix is a *carried* runtime invariant: every polymorphic
(`arity ≠ 0`) binding in the reachable context sits at a **nonzero** level (and — automatically for the
`genAtV` schemes the runtime actually builds — that level occurs among its body's levels). Established
at a nonzero initial ambient level and preserved by every `let_poly` step (which generalizes at its own
— necessarily nonzero — ambient level, per the inline-strict `let_poly` shape). -/

/-- Every polymorphic (`arity ≠ 0`) binding of `Γ` has a nonzero level that occurs among its body's
levels. `lvl` in `body.levels` is automatic for `genAtV lvl d` (arity `≠ 0 ⟹ lvl ∈ d.levels`); the
content is nonzero-ness. -/
def CtxPolyBd (Γ : Ctx) : Prop :=
  ∀ b ∈ Γ, b.2.arity ≠ 0 → b.2.level ≠ 0 ∧ b.2.level ∈ b.2.body.levels

/-- **Bridge:** `CtxPolyBd Γ` + `CtxWfV ℓ Γ` derive the free-variable-aware substitution precondition
`PolyAboveFV ℓ Γ e` for **every** term `e`. A looked-up poly binding's level is `≠ 0` (from
`CtxPolyBd`) and `< ℓ` hence `≠ ℓ` (from `CtxWfV`, since that level is one of its body levels). -/
theorem polyAboveFV_of_ctxPolyBd {ℓ : Nat} {Γ : Ctx} {e : Tree.Node m}
    (hnz : CtxPolyBd Γ) (hwf : CtxWfV ℓ Γ) : PolyAboveFV ℓ Γ e := by
  intro x _ s hlk
  by_cases h0 : s.arity = 0
  · exact Or.inl h0
  · obtain ⟨hne0, hmem⟩ := hnz (x, s) (lookup_mem hlk) h0
    exact Or.inr ⟨hne0, by have := hwf (x, s) (lookup_mem hlk) s.level hmem; omega⟩

/-- **Preservation of `CtxPolyBd` under a `let_poly` binding** (`genAtV lvl d`, `lvl ≠ 0`). The new
binding is either mono-like (`arity = 0`, vacuous) or poly, in which case its level is `lvl ≠ 0` and
`arity ≠ 0 ⟹ lvl ∈ d.levels` by the definition of `genAtV`. -/
theorem ctxPolyBd_cons_genAtV {Γ : Ctx} {x : String} {lvl : Nat} {d : Ty}
    (hlvl : lvl ≠ 0) (hΓ : CtxPolyBd Γ) :
    CtxPolyBd ((x, Scheme.genAtV lvl d) :: Γ) := by
  intro b hb harity
  rcases List.mem_cons.mp hb with h | h
  · subst h
    refine ⟨hlvl, ?_⟩
    simp only [Scheme.genAtV] at harity ⊢
    have hpos : 0 < (d.levels.filter (· = lvl)).length := Nat.pos_of_ne_zero harity
    obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos hpos
    rw [List.mem_filter] at ha
    obtain ⟨hmem, heq⟩ := ha
    simp only [decide_eq_true_eq] at heq
    exact heq ▸ hmem
  · exact hΓ b h harity

/-- **The per-binding poly-boundedness fact for a `genAtV` scheme** (the `EnvWf.cons`/`StackWfV`
`hpoly` obligation): a `genAtV lvl d` binding with `lvl ≠ 0` sits at a nonzero level that occurs
among its body's levels whenever it is genuinely polymorphic (`arity ≠ 0`). -/
theorem schemePolyBd_genAtV {lvl : Nat} {d : Ty} (hlvl : lvl ≠ 0) :
    (Scheme.genAtV lvl d).arity ≠ 0 →
      (Scheme.genAtV lvl d).level ≠ 0 ∧
        (Scheme.genAtV lvl d).level ∈ (Scheme.genAtV lvl d).body.levels := by
  intro harity
  refine ⟨hlvl, ?_⟩
  simp only [Scheme.genAtV] at harity ⊢
  have hpos : 0 < (d.levels.filter (· = lvl)).length := Nat.pos_of_ne_zero harity
  obtain ⟨a, ha⟩ := List.exists_mem_of_length_pos hpos
  rw [List.mem_filter] at ha
  obtain ⟨hmem, heq⟩ := ha
  simp only [decide_eq_true_eq] at heq
  exact heq ▸ hmem

/-- The `hpoly` obligation for a monomorphic scheme is vacuous (`arity = 0`). -/
theorem schemePolyBd_mono {t : Ty} :
    (Scheme.mono t).arity ≠ 0 →
      (Scheme.mono t).level ≠ 0 ∧ (Scheme.mono t).level ∈ (Scheme.mono t).body.levels :=
  fun h => absurd rfl h

/-- A monomorphic binding preserves `CtxPolyBd` (its `arity = 0`, so the obligation is vacuous). -/
theorem ctxPolyBd_cons_mono {Γ : Ctx} {x : String} {t : Ty} (hΓ : CtxPolyBd Γ) :
    CtxPolyBd ((x, Scheme.mono t) :: Γ) := by
  intro b hb harity
  rcases List.mem_cons.mp hb with h | h
  · subst h; exact absurd rfl harity
  · exact hΓ b h harity

/-! ## Level-native type substitution — the instantiation-direction re-typing lemma -/

/-- **Instantiation-direction type substitution for `HasType`.** A derivation re-types under an
**outer** level-`ℓ` substitution `substAt ℓ σ` (`ℓ ≠ 0`, `ℓ < lvl`, `σ`'s levels `≤ ℓ`, context
polymorphic bindings above `ℓ`). The `let_poly` arm reconstructs via `substCtxAt_cons_genAtV`
(level-native, no `LevelMap`); fires non-vacuously for arbitrarily deep nesting. -/
theorem hasType_subst {ℓ : Nat} (hℓ : ℓ ≠ 0) (σ : Nat → Ty)
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ)
    {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    (h : HasType lvl Γ e τ ε) (hlt : ℓ < lvl) (hΓ : PolyAboveFV ℓ Γ e) :
    HasType lvl (substCtxAt ℓ σ Γ) e (Ty.substAt ℓ σ τ) (Ty.substAt ℓ σ ε) := by
  have hσle : ∀ i, ∀ l ∈ (σ i).levels, l ≤ ℓ := fun i l hl => by
    rcases hσ i l hl with h | h <;> omega
  revert hlt hΓ
  induction h with
  | @var lvl Γ x s args ε a hl =>
      intro hlt hΓ
      have hdisj : s.arity = 0 ∨ (ℓ ≠ s.level ∧ ∀ i, ∀ j, j ∉ Ty.freeVarsAt s.level (σ i)) := by
        by_cases h0 : s.arity = 0
        · exact Or.inl h0
        · obtain ⟨hlvl0, hlvlℓ⟩ :=
            (hΓ x (by simp [Tree.Node.freeVars]) s hl).resolve_left h0
          refine Or.inr ⟨Ne.symm hlvlℓ, ?_⟩
          intro i j hj
          rcases hσ i s.level (Ty.mem_levels_of_mem_freeVarsAt hj) with h | h
          · exact hlvl0 h
          · exact hlvlℓ h
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
        · exact Nat.lt_of_le_of_lt (hσle i l hi) (Nat.lt_of_lt_of_le hlt hle)
      · have hb := ih (Nat.lt_of_lt_of_le hlt hle)
          (polyAboveFV_bind (Or.inl rfl) hΓ
            (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩))
        rw [substCtxAt_cons, substSchemeVAt_mono] at hb
        exact hb
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg ihf iharg =>
      intro hlt hΓ
      have hf' := ihf hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy))
      simp only [Ty.substAt] at hf'
      exact HasType.app hf' (Ty.substAt_effWeaken ℓ σ hw)
        (iharg hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_right _ hy)))
  | @let_ lvl lvl' Γ x defn body defnTy bodyTy ε a hdefn hle hfv hbody ihdefn ihbody =>
      intro hlt hΓ
      have hb := ihbody (Nat.lt_of_lt_of_le hlt hle)
        (polyAboveFV_bind (Or.inl rfl) hΓ
          (fun y hy hne => List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne⟩)))
      rw [substCtxAt_cons, substSchemeVAt_mono] at hb
      refine HasType.let_ (ihdefn hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy)))
        hle ?_ hb
      intro l hl
      rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
      · exact hfv l hl'
      · exact Nat.lt_of_le_of_lt (hσle i l hi) (Nat.lt_of_lt_of_le hlt hle)
  | @let_poly lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a hstrict hfv hbodydefn hcw
      hbody ihdefn ihbody =>
      intro hlt hΓ
      have hne : ℓ ≠ lvl := Nat.ne_of_lt hlt
      have hcleanlvl : ∀ i, lvl ∉ (σ i).levels := fun i hmem => absurd (hσ i lvl hmem) (by omega)
      have hΓdefn : PolyAboveFV ℓ Γ ⟨.Lambda lx lbody, la⟩ :=
        polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy)
      have hΓdb : PolyAboveFV ℓ ((lx, Scheme.mono argTy) :: Γ) lbody :=
        polyAboveFV_bind (Or.inl rfl) hΓdefn
          (fun y hy hne2 => List.mem_filter.mpr ⟨hy, by simpa using hne2⟩)
      have hbd := ihdefn (lt_trans hlt hstrict) hΓdb
      rw [substCtxAt_cons, substSchemeVAt_mono] at hbd
      have hfv' : ∀ l ∈ (Ty.substAt ℓ σ argTy).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
        · exact hfv l hl'
        · exact Nat.lt_of_le_of_lt (hσle i l hi) (lt_trans hlt hstrict)
      have hΓ1 : PolyAboveFV ℓ ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body :=
        polyAboveFV_bind (Or.inr (by simp only [Scheme.genAtV]; omega)) hΓ
          (fun y hy hne => List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne⟩))
      have hbodyIH := ihbody (by omega : ℓ < lvl + 1) hΓ1
      rw [substCtxAt_cons_genAtV hne hcleanlvl] at hbodyIH
      simp only [Ty.substAt] at hbodyIH
      exact HasType.let_poly hstrict hfv' hbd (ctxWfV_substCtxAt hlt hσle hcw) hbodyIH
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
    (hΓpa : PolyAboveFV ℓ Γ ⟨.Lambda x lbody, la⟩)
    (hΓwf : CtxWfV ℓ Γ)
    (args : List Ty)
    (hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = ℓ) :
    HasType ℓ Γ ⟨.Lambda x lbody, la⟩
      ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) ε := by
  set defnTy : Ty := .fun argTy εb retTy with hdefn
  have hΓpa' : PolyAboveFV ℓ ((x, Scheme.mono argTy) :: Γ) lbody :=
    polyAboveFV_bind (Or.inl rfl) hΓpa
      (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩)
  by_cases h0 : (Scheme.genAtV ℓ defnTy).arity = 0
  · rw [Scheme.instantiateV, if_pos h0, ← Ty.substAt_var_self ℓ defnTy]
    have hσ : ∀ i, ∀ l ∈ ((fun i => Ty.var ℓ i) i).levels, l = 0 ∨ l = ℓ := by
      intro i l hl; simp only [Ty.levels, List.mem_singleton] at hl; exact Or.inr hl
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
    have hσ : ∀ i, ∀ l ∈ (args.getD i (.var ℓ i)).levels, l = 0 ∨ l = ℓ := by
      intro i l hl
      rcases lt_or_ge i args.length with hi | hi
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hl
        exact hargs _ (List.getElem_mem hi) l hl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none] at hl
        simp only [Ty.levels, List.mem_singleton] at hl; exact Or.inr hl
    have hb := hasType_subst hℓ (fun i => args.getD i (.var ℓ i)) hσ hbody hlt hΓpa'
    rw [substCtxAt_cons, substSchemeVAt_mono] at hb
    have hlam := HasType.lam (a := la) (ε := ε) (le_of_lt hlt)
      (by intro l hl
          rcases Ty.mem_levels_substAt hl with hl' | ⟨i, hi⟩
          · exact hfv l hl'
          · rcases hσ i l hi with h | h <;> omega) hb
    have hfix : substCtxAt ℓ (fun i => args.getD i (.var ℓ i)) Γ = Γ := substCtxAt_fix hΓwf
    rw [hfix] at hlam
    simpa only [Ty.substAt, hdefn] using hlam

/-! ## Non-strict re-typing at the generalization level (`NoGenAt` / `hasType_substAt_le`)

`hasType_subst`'s precondition `ℓ < lvl` is strictly stronger than soundness needs: tracing its
induction, the strict inequality is consumed in **exactly one arm** — `let_poly`, as the fact
`hne : ℓ ≠ lvl` (the opening level must differ from that node's own generalization level, so
`substAt ℓ` never touches its generalized region). Every other arm needs only `ℓ ≤ lvl`.

But some value-restricted closures are generalized at *exactly* their body's sublevel `lvl' = ℓ`
(e.g. `\x. perform "op" x`, whose ground arg type leaves `lvl'` unforced; see the `defnPerf` witness
in `section Examples`). For those the strict keystone cannot fire. The fix is a **derivation-level
side condition** `NoGenAt ℓ h` — "no `let_poly` reachable in `h` generalizes at exactly `ℓ`" —
which the `let_poly` arm consumes directly as its `hne`, replacing the strict inequality. This is
genuinely a parallel derivation predicate (indexed by the `HasType` proof): a `let_poly` term node
generalizes at `ℓ` depends on the *level the derivation assigned it*, not off the bare syntax. -/

/-- **No reachable `let_poly` generalizes at exactly `ℓ`** (a parallel-to-`HasType` predicate,
indexed by the derivation). The `let_poly` arm requires that node's own generalization level `lvl`
to differ from `ℓ` and recurses on both sub-derivations; every other constructor recurses on its
sub-derivation(s) unconditionally. Consumed by `hasType_substAt_le` to admit `ℓ ≤ lvl`. -/
inductive NoGenAt {m : Type} (ℓ : Nat) :
    {lvl : Nat} → {Γ : Ctx} → {e : Tree.Node m} → {τ ε : Ty} →
    HasType lvl Γ e τ ε → Prop where
  | var {lvl Γ x s args ε a} (hl : Γ.lookup x = some s) :
      NoGenAt ℓ (HasType.var (lvl := lvl) (Γ := Γ) (x := x) (s := s) (args := args)
        (ε := ε) (a := a) hl)
  | lam {lvl lvl' Γ x body argTy εb retTy ε a}
      (hle : lvl ≤ lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono argTy) :: Γ) body retTy εb} :
      NoGenAt ℓ hbody → NoGenAt ℓ (HasType.lam (ε := ε) (a := a) hle hfv hbody)
  | app {lvl Γ f arg argTy εf retTy ε a}
      {hf : HasType lvl Γ f (.fun argTy εf retTy) ε} {hw : Ty.EffWeaken εf ε}
      {harg : HasType lvl Γ arg argTy ε} :
      NoGenAt ℓ hf → NoGenAt ℓ harg → NoGenAt ℓ (HasType.app (a := a) hf hw harg)
  | let_ {lvl lvl' Γ x defn body defnTy bodyTy ε a}
      {hdefn : HasType lvl Γ defn defnTy ε} (hle : lvl ≤ lvl')
      (hfv : ∀ l ∈ defnTy.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono defnTy) :: Γ) body bodyTy ε} :
      NoGenAt ℓ hdefn → NoGenAt ℓ hbody →
      NoGenAt ℓ (HasType.let_ (a := a) hdefn hle hfv hbody)
  | let_poly {lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a}
      (hstrict : lvl < lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      {hbodydefn : HasType lvl' ((lx, .mono argTy) :: Γ) lbody retTy εb} {hcw : CtxWfV lvl Γ}
      {hbody : HasType (lvl + 1) ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body bodyTy ε} :
      lvl ≠ ℓ → NoGenAt ℓ hbodydefn → NoGenAt ℓ hbody →
      NoGenAt ℓ (HasType.let_poly (a := a) (la := la) hstrict hfv hbodydefn hcw hbody)
  | int {lvl Γ n ε a} :
      NoGenAt ℓ (HasType.int (m := m) (lvl := lvl) (Γ := Γ) (n := n) (ε := ε) (a := a))
  | str {lvl Γ s ε a} :
      NoGenAt ℓ (HasType.str (m := m) (lvl := lvl) (Γ := Γ) (s := s) (ε := ε) (a := a))
  | bin {lvl Γ b ε a} :
      NoGenAt ℓ (HasType.bin (m := m) (lvl := lvl) (Γ := Γ) (b := b) (ε := ε) (a := a))
  | builtin {lvl Γ id s args ε a} (hs : Builtins.scheme id = some s) :
      NoGenAt ℓ (HasType.builtin (lvl := lvl) (Γ := Γ) (args := args) (ε := ε) (a := a) hs)
  | tail {lvl Γ elem ε a} :
      NoGenAt ℓ (HasType.tail (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | cons {lvl Γ elem ε a} :
      NoGenAt ℓ (HasType.cons (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | tag {lvl Γ l elem tail ε a} :
      NoGenAt ℓ (HasType.tag (m := m) (lvl := lvl) (Γ := Γ) (l := l) (elem := elem)
        (tail := tail) (ε := ε) (a := a))
  | nocases {lvl Γ ret ε a} :
      NoGenAt ℓ (HasType.nocases (m := m) (lvl := lvl) (Γ := Γ) (ret := ret) (ε := ε)
        (a := a))
  | case_ {lvl Γ l inner eff ret tail ε a} :
      NoGenAt ℓ (HasType.case_ (m := m) (lvl := lvl) (Γ := Γ) (l := l) (inner := inner)
        (eff := eff) (ret := ret) (tail := tail) (ε := ε) (a := a))
  | select {lvl Γ l fieldTy tail ε a} :
      NoGenAt ℓ (HasType.select (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (tail := tail) (ε := ε) (a := a))
  | extend {lvl Γ l fieldTy row ε a} :
      NoGenAt ℓ (HasType.extend (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (row := row) (ε := ε) (a := a))
  | overwrite {lvl Γ l newTy oldTy tail ε a} :
      NoGenAt ℓ (HasType.overwrite (m := m) (lvl := lvl) (Γ := Γ) (l := l) (newTy := newTy)
        (oldTy := oldTy) (tail := tail) (ε := ε) (a := a))
  | empty {lvl Γ ε a} :
      NoGenAt ℓ (HasType.empty (m := m) (lvl := lvl) (Γ := Γ) (ε := ε) (a := a))
  | perform {lvl Γ l aa b μ ε ann} :
      NoGenAt ℓ (HasType.perform (m := m) (lvl := lvl) (Γ := Γ) (l := l) (a := aa) (b := b)
        (μ := μ) (ε := ε) (ann := ann))
  | handle {lvl Γ l lift reply tail ret ε ann} :
      NoGenAt ℓ (HasType.handle (m := m) (lvl := lvl) (Γ := Γ) (l := l) (lift := lift)
        (reply := reply) (tail := tail) (ret := ret) (ε := ε) (ann := ann))
  | conv {lvl Γ e τ τ' ε ε'} {h : HasType lvl Γ e τ ε}
      (hτ : Ty.TyEquiv τ τ') (hε : Ty.TyEquiv ε ε') :
      NoGenAt ℓ h → NoGenAt ℓ (HasType.conv h hτ hε)

/-- **Non-strict companion to `hasType_subst`.** Re-types a derivation under an outer level-`ℓ`
substitution with the *non-strict* `ℓ ≤ lvl` (vs `hasType_subst`'s `ℓ < lvl`), paying for it with
the derivation-level side condition `NoGenAt ℓ h`. The `let_poly` arm takes its needed `ℓ ≠ lvl`
from `NoGenAt` (which — combined with `ℓ ≤ lvl` — recovers the strict `ℓ < lvl` that arm still needs
internally); the `lam`/`let_` arms recover their `l < lvl'` level bounds via
`mem_levels_substAt_strong` (which supplies `ℓ ∈ argTy.levels`, whence `hfv ℓ`) at `lvl' = ℓ`. -/
theorem hasType_substAt_le {ℓ : Nat} (hℓ : ℓ ≠ 0) (σ : Nat → Ty)
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ)
    {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    {h : HasType lvl Γ e τ ε} (hng : NoGenAt ℓ h) (hlt : ℓ ≤ lvl)
    (hΓ : PolyAboveFV ℓ Γ e) :
    HasType lvl (substCtxAt ℓ σ Γ) e (Ty.substAt ℓ σ τ) (Ty.substAt ℓ σ ε) := by
  have hσle : ∀ i, ∀ l ∈ (σ i).levels, l ≤ ℓ := fun i l hl => by
    rcases hσ i l hl with h | h <;> omega
  revert hlt hΓ
  induction hng with
  | @var lvl Γ x s args ε a hl =>
      intro hlt hΓ
      have hdisj : s.arity = 0 ∨ (ℓ ≠ s.level ∧ ∀ i, ∀ j, j ∉ Ty.freeVarsAt s.level (σ i)) := by
        by_cases h0 : s.arity = 0
        · exact Or.inl h0
        · obtain ⟨hlvl0, hlvlℓ⟩ :=
            (hΓ x (by simp [Tree.Node.freeVars]) s hl).resolve_left h0
          refine Or.inr ⟨Ne.symm hlvlℓ, ?_⟩
          intro i j hj
          rcases hσ i s.level (Ty.mem_levels_of_mem_freeVarsAt hj) with h | h
          · exact hlvl0 h
          · exact hlvlℓ h
      rw [substAt_instantiateV_scheme hdisj args]
      exact HasType.var (substCtxAt_lookup hl)
  | @builtin lvl Γ id s args ε a hs =>
      intro hlt hΓ
      rw [substAt_instantiateV_closed (by rw [Builtins.scheme_level hs]; exact hℓ)
            (Builtins.scheme_no_level hℓ hs) args,
          Builtins.scheme_substSchemeVAt hℓ σ hs]
      exact HasType.builtin hs
  | @lam lvl lvl' Γ x body argTy εb retTy ε a hle hfv hbody nghbody ih =>
      intro hlt hΓ
      simp only [Ty.substAt]
      refine HasType.lam hle ?_ ?_
      · intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hfv l hl'
        · exact Nat.lt_of_le_of_lt (hσle i l hi) (hfv ℓ hm)
      · have hb := ih (le_trans hlt hle)
          (polyAboveFV_bind (Or.inl rfl) hΓ
            (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩))
        rw [substCtxAt_cons, substSchemeVAt_mono] at hb
        exact hb
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg nghf ngharg ihf iharg =>
      intro hlt hΓ
      have hf' := ihf hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy))
      simp only [Ty.substAt] at hf'
      exact HasType.app hf' (Ty.substAt_effWeaken ℓ σ hw)
        (iharg hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_right _ hy)))
  | @let_ lvl lvl' Γ x defn body defnTy bodyTy ε a hdefn hle hfv hbody ngd ngb ihdefn ihbody =>
      intro hlt hΓ
      have hb := ihbody (le_trans hlt hle)
        (polyAboveFV_bind (Or.inl rfl) hΓ
          (fun y hy hne => List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne⟩)))
      rw [substCtxAt_cons, substSchemeVAt_mono] at hb
      refine HasType.let_ (ihdefn hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy)))
        hle ?_ hb
      intro l hl
      rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
      · exact hfv l hl'
      · exact Nat.lt_of_le_of_lt (hσle i l hi) (hfv ℓ hm)
  | @let_poly lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a hstrict hfv hbodydefn hcw hbody
      hne ngd ngb ihdefn ihbody =>
      intro hlt hΓ
      have hlts : ℓ < lvl := lt_of_le_of_ne hlt (Ne.symm hne)
      have hne' : ℓ ≠ lvl := Nat.ne_of_lt hlts
      have hcleanlvl : ∀ i, lvl ∉ (σ i).levels := fun i hmem => absurd (hσ i lvl hmem) (by omega)
      have hΓdefn : PolyAboveFV ℓ Γ ⟨.Lambda lx lbody, la⟩ :=
        polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy)
      have hΓdb : PolyAboveFV ℓ ((lx, Scheme.mono argTy) :: Γ) lbody :=
        polyAboveFV_bind (Or.inl rfl) hΓdefn
          (fun y hy hne2 => List.mem_filter.mpr ⟨hy, by simpa using hne2⟩)
      have hbd := ihdefn (le_of_lt (lt_trans hlts hstrict)) hΓdb
      rw [substCtxAt_cons, substSchemeVAt_mono] at hbd
      have hfv' : ∀ l ∈ (Ty.substAt ℓ σ argTy).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hfv l hl'
        · exact Nat.lt_of_le_of_lt (hσle i l hi) (hfv ℓ hm)
      have hΓ1 : PolyAboveFV ℓ ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body :=
        polyAboveFV_bind (Or.inr (by simp only [Scheme.genAtV]; omega)) hΓ
          (fun y hy hne2 => List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne2⟩))
      have hbodyIH := ihbody (by omega : ℓ ≤ lvl + 1) hΓ1
      rw [substCtxAt_cons_genAtV hne' hcleanlvl] at hbodyIH
      simp only [Ty.substAt] at hbodyIH
      exact HasType.let_poly hstrict hfv' hbd (ctxWfV_substCtxAt hlts hσle hcw) hbodyIH
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
  | @conv lvl Γ e τ τ' ε ε' h hτ hε ngh ih =>
      intro hlt hΓ
      exact HasType.conv (ih hlt hΓ) (Ty.substAt_tyEquiv ℓ σ hτ) (Ty.substAt_tyEquiv ℓ σ hε)

/-- **The non-strict readiness keystone (`NoGenAt`-aware).** The `ℓ ≤ lvl'` companion to
`genAtV_instantiate_lam_ready`: a value-restricted lambda whose body sublevel `lvl'` may *equal* the
generalization level `ℓ` (as for `\x. perform "op" x`) still has every instantiation of its
`genAtV ℓ`-scheme realised as a genuine `substAt ℓ` re-typing of its own body derivation — provided
that body derivation satisfies `NoGenAt ℓ` (no inner `let_poly` generalizes at `ℓ`). Delegates to
`hasType_substAt_le` in place of `hasType_subst`. -/
theorem genAtV_instantiate_lam_ready_le {ℓ : Nat} (hℓ : ℓ ≠ 0)
    {lvl' : Nat} {Γ : Ctx} {x : String} {lbody : Tree.Node m} {la : m}
    {argTy εb retTy ε : Ty}
    (hlt : ℓ ≤ lvl')
    (hfv : ∀ l ∈ argTy.levels, l < lvl')
    {hbody : HasType lvl' ((x, .mono argTy) :: Γ) lbody retTy εb}
    (hng : NoGenAt ℓ hbody)
    (hΓpa : PolyAboveFV ℓ Γ ⟨.Lambda x lbody, la⟩)
    (hΓwf : CtxWfV ℓ Γ)
    (args : List Ty)
    (hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = ℓ) :
    HasType ℓ Γ ⟨.Lambda x lbody, la⟩
      ((Scheme.genAtV ℓ (.fun argTy εb retTy)).instantiateV args) ε := by
  set defnTy : Ty := .fun argTy εb retTy with hdefn
  have hΓpa' : PolyAboveFV ℓ ((x, Scheme.mono argTy) :: Γ) lbody :=
    polyAboveFV_bind (Or.inl rfl) hΓpa
      (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩)
  by_cases h0 : (Scheme.genAtV ℓ defnTy).arity = 0
  · rw [Scheme.instantiateV, if_pos h0, ← Ty.substAt_var_self ℓ defnTy]
    have hσ : ∀ i, ∀ l ∈ ((fun i => Ty.var ℓ i) i).levels, l = 0 ∨ l = ℓ := by
      intro i l hl; simp only [Ty.levels, List.mem_singleton] at hl; exact Or.inr hl
    have hb := hasType_substAt_le hℓ (fun i => Ty.var ℓ i) hσ hng hlt hΓpa'
    rw [substCtxAt_cons, substSchemeVAt_mono] at hb
    have hlam := HasType.lam (a := la) (ε := ε) hlt
      (by intro l hl
          rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
          · exact hfv l hl'
          · simp only [Ty.levels, List.mem_singleton] at hi; rw [hi]; exact hfv ℓ hm) hb
    have hfix : substCtxAt ℓ (fun i => Ty.var ℓ i) Γ = Γ := substCtxAt_fix hΓwf
    rw [hfix] at hlam
    simpa only [Ty.substAt, hdefn] using hlam
  · rw [Scheme.instantiateV, if_neg h0]
    have hσ : ∀ i, ∀ l ∈ (args.getD i (.var ℓ i)).levels, l = 0 ∨ l = ℓ := by
      intro i l hl
      rcases lt_or_ge i args.length with hi | hi
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hl
        exact hargs _ (List.getElem_mem hi) l hl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none] at hl
        simp only [Ty.levels, List.mem_singleton] at hl; exact Or.inr hl
    have hb := hasType_substAt_le hℓ (fun i => args.getD i (.var ℓ i)) hσ hng hlt hΓpa'
    rw [substCtxAt_cons, substSchemeVAt_mono] at hb
    have hlam := HasType.lam (a := la) (ε := ε) hlt
      (by intro l hl
          rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
          · exact hfv l hl'
          · have hℓlt := hfv ℓ hm; rcases hσ i l hi with h | h <;> omega) hb
    have hfix : substCtxAt ℓ (fun i => args.getD i (.var ℓ i)) Γ = Γ := substCtxAt_fix hΓwf
    rw [hfix] at hlam
    simpa only [Ty.substAt, hdefn] using hlam

/-- **Lambda inversion carrying `NoGenAt` to the body.** `inv_lambda` recovers a lambda's `lam`
components up to `TyEquiv`; this variant additionally transports a `NoGenAt ℓ` fact on the whole
derivation down to the reconstructed body derivation — the bridge the closure-node wrapper needs
to feed `genAtV_instantiate_lam_ready_le`. -/
theorem inv_lambda_noGenAt {ℓ lvl : Nat} {Γ : Ctx} {x : String} {body : Tree.Node m} {a : m}
    {τ ε : Ty} {h : HasType lvl Γ ⟨.Lambda x body, a⟩ τ ε} (hng : NoGenAt ℓ h) :
    ∃ lvl' argTy εb retTy, ∃ hbody : HasType lvl' ((x, .mono argTy) :: Γ) body retTy εb,
      lvl ≤ lvl' ∧ (∀ l ∈ argTy.levels, l < lvl') ∧ NoGenAt ℓ hbody ∧
      Ty.TyEquiv (.fun argTy εb retTy) τ := by
  generalize he : (⟨.Lambda x body, a⟩ : Tree.Node m) = enode at h
  revert he
  induction hng with
  | @lam lvl lvl' Γ x' body' argTy εb retTy ε a hle hfv hbody nghbody ih =>
      intro he; cases he
      exact ⟨lvl', argTy, εb, retTy, hbody, hle, hfv, nghbody, .refl _⟩
  | @conv lvl Γ e' τ' τ'' ε' ε'' hh hτ hε ngh ih =>
      intro he
      obtain ⟨lvl', argTy, εb, retTy, hbody, hle, hfv, nghbody, heq⟩ := ih he
      exact ⟨lvl', argTy, εb, retTy, hbody, hle, hfv, nghbody, heq.trans hτ⟩
  | _ => intro he; exact absurd he (by simp)

/-- **Level-monotone `NoGenAt`.** The ambient level of a `HasType` derivation only ever *increases*
as one descends (`lam`/`let_` keep the body at `≥` level; `let_poly` bumps its body to `lvl+1`;
`app`/`conv` keep it fixed), so every reachable `let_poly` generalizes at a level `≥` the root's —
whence a derivation typed at level `lvl` satisfies `NoGenAt ℓ` for **every** `ℓ < lvl`. This is the
non-narrowing tool that discharges the closure-readiness wrapper's `NoGenAt lvl` obligation whenever
the value-restricted lambda's body sublevel is *strictly* above the generalization level
(`lvl' > lvl`), with **no** external `NoGenAt` witness. (The residual `lvl' = lvl` case — e.g. the
`defnPerf` effect-tail witness in `section Examples` — still needs a genuine `NoGenAt`, so this
does not by itself close the `let_poly` preservation site.) -/
theorem noGenAt_of_lt {ℓ : Nat} :
    ∀ {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
      (h : HasType lvl Γ e τ ε), ℓ < lvl → NoGenAt ℓ h := by
  intro lvl Γ e τ ε h
  induction h with
  | var hl => exact fun _ => NoGenAt.var hl
  | lam hle hfv hbody ih => exact fun hlt => NoGenAt.lam hle hfv (ih (lt_of_lt_of_le hlt hle))
  | app hf hw harg ihf iharg => exact fun hlt => NoGenAt.app (hw := hw) (ihf hlt) (iharg hlt)
  | let_ hdefn hle hfv hbody ihd ihb =>
      exact fun hlt => NoGenAt.let_ hle hfv (ihd hlt) (ihb (lt_of_lt_of_le hlt hle))
  | let_poly hstrict hfv hbodydefn hcw hbody ihd ihb =>
      exact fun hlt =>
        NoGenAt.let_poly (hcw := hcw) hstrict hfv (Nat.ne_of_lt hlt).symm
          (ihd (lt_trans hlt hstrict)) (ihb (Nat.lt_succ_of_lt hlt))
  | int => exact fun _ => NoGenAt.int
  | str => exact fun _ => NoGenAt.str
  | bin => exact fun _ => NoGenAt.bin
  | builtin hs => exact fun _ => NoGenAt.builtin hs
  | tail => exact fun _ => NoGenAt.tail
  | cons => exact fun _ => NoGenAt.cons
  | tag => exact fun _ => NoGenAt.tag
  | nocases => exact fun _ => NoGenAt.nocases
  | case_ => exact fun _ => NoGenAt.case_
  | select => exact fun _ => NoGenAt.select
  | extend => exact fun _ => NoGenAt.extend
  | overwrite => exact fun _ => NoGenAt.overwrite
  | empty => exact fun _ => NoGenAt.empty
  | perform => exact fun _ => NoGenAt.perform
  | handle => exact fun _ => NoGenAt.handle
  | conv _ hτ hε ih => exact fun hlt => NoGenAt.conv hτ hε (ih hlt)

/-- **`NoGenAt lvl` of the reconstructed defn-lambda, for free** (the payoff of the strict-sublevel
`let_poly` discipline). Since the defn lambda's body descends **strictly** (`lvl < lvl'`),
`noGenAt_of_lt` supplies `NoGenAt lvl` of that body, and `NoGenAt.lam` wraps it. This is exactly the
`NoGenAt lvl h` premise the closure-readiness wrapper (`genAtV_closure_ready_value_node`) needs —
handed over for free at every `let_poly` inversion site, discharging the G1 Caveat-5 gap. -/
theorem noGenAt_letpoly_defn {m : Type} {lvl lvl' : Nat} {Γ : Ctx} {lx : String}
    {lbody : Tree.Node m} {la : m} {argTy εb retTy ε : Ty}
    (hstrict : lvl < lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
    (hbodydefn : HasType lvl' ((lx, .mono argTy) :: Γ) lbody retTy εb) :
    NoGenAt lvl (HasType.letpoly_defn (la := la) (ε := ε) hstrict hfv hbodydefn) :=
  NoGenAt.lam (le_of_lt hstrict) hfv (noGenAt_of_lt hbodydefn hstrict)

/-! ## The runtime-restricted judgment `HasTypeRT` (gap 1: var-preservation groundness)

At the var-preservation site (`Soundness.lean`, both engines), the control is a **bare** variable
node `⟨.Variable x⟩` with `hty : HasType lvl Γ ⟨.Variable x⟩ (s.instantiateV args) ε`; and
`envwf_lookup` supplies `hvty : ∀ args, (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level) →
HasTypeV v (s.instantiateV args)`. Preservation needs `hvty args` for the **specific** `args` the
derivation chose — i.e. the args side-condition `∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level`.
`HasType.var` records **no** constraint on `args`, and one **must not** be added there (it would
reject legitimate *typing-time* instantiations — see `hbody_ref` in `section Examples`, whose
non-ground arg `[.var 2 0]` at level 2 is a perfectly valid static subderivation).

The fix is a **runtime-restricted** predicate `HasTypeRT h` (indexed by the `HasType` derivation
`h`, mirroring `NoGenAt`) that a running well-typed machine state carries for its *control*
derivation. Its `var`/`builtin` arms additionally record the args side-condition; the
var-preservation site then discharges `hvty args` directly (`inv_var_rt`).

**Design correction over the Session-D sketch ("every other arm is a verbatim structural copy"):**
the `lam` arm must **not** recurse into the lambda body, and `let_poly` must **not** recurse into
its lambda-defn. A lambda's body is never evaluated *as a control* until its closure is applied, at
which point the keystone (`genAtV_instantiate_lam_ready`/`..._le`) re-types it via `substAt` with
**ground** args — re-establishing `HasTypeRT` there. Recursing into lambda bodies would make even
the legitimate whole referencing program (`section Examples`, `let a = \x.x in let c = \w. a w in
c`) fail to be `HasTypeRT`, because its `\w. a w` body carries the non-ground arg `[.var 2 0]`
(level 2 ≠ `a.level`=1). By stopping at lambda bodies, `HasTypeRT` (a) admits that whole program and
(b) still forces every var node that is *actually reachable as a control* (never under an
un-applied lambda) to have bounded args. `app`/`let_` recurse (both sub-terms become controls);
`conv` recurses; literals/atomics are leaves. -/

/-- **Runtime-restricted typing** (indexed by a `HasType` derivation). `var`/`builtin` arms carry
the args side-condition `∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level`; `lam`/`let_poly` do
**not** recurse into the (un-applied) lambda body; `app`/`let_`/`conv` recurse. Carried on the
control derivation of a running machine state (`MStateWf`) so var-preservation can discharge the
readiness side-condition it needs. -/
inductive HasTypeRT {m : Type} :
    {lvl : Nat} → {Γ : Ctx} → {e : Tree.Node m} → {τ ε : Ty} →
    HasType lvl Γ e τ ε → Prop where
  | var {lvl Γ x s args ε a} (hl : Γ.lookup x = some s)
      (hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level) :
      HasTypeRT (HasType.var (lvl := lvl) (Γ := Γ) (x := x) (s := s) (args := args)
        (ε := ε) (a := a) hl)
  | lam {lvl lvl' Γ x body argTy εb retTy ε a}
      (hle : lvl ≤ lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono argTy) :: Γ) body retTy εb} :
      HasTypeRT (HasType.lam (ε := ε) (a := a) hle hfv hbody)
  | app {lvl Γ f arg argTy εf retTy ε a}
      {hf : HasType lvl Γ f (.fun argTy εf retTy) ε} {hw : Ty.EffWeaken εf ε}
      {harg : HasType lvl Γ arg argTy ε} :
      HasTypeRT hf → HasTypeRT harg → HasTypeRT (HasType.app (a := a) hf hw harg)
  | let_ {lvl lvl' Γ x defn body defnTy bodyTy ε a}
      {hdefn : HasType lvl Γ defn defnTy ε} (hle : lvl ≤ lvl')
      (hfv : ∀ l ∈ defnTy.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono defnTy) :: Γ) body bodyTy ε} :
      HasTypeRT hdefn → HasTypeRT hbody →
      HasTypeRT (HasType.let_ (a := a) hdefn hle hfv hbody)
  | let_poly {lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a}
      (hstrict : lvl < lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      {hbodydefn : HasType lvl' ((lx, .mono argTy) :: Γ) lbody retTy εb} {hcw : CtxWfV lvl Γ}
      {hbody : HasType (lvl + 1) ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body bodyTy ε} :
      HasTypeRT hbody →
      HasTypeRT (HasType.let_poly (a := a) (la := la) hstrict hfv hbodydefn hcw hbody)
  | int {lvl Γ n ε a} :
      HasTypeRT (HasType.int (m := m) (lvl := lvl) (Γ := Γ) (n := n) (ε := ε) (a := a))
  | str {lvl Γ s ε a} :
      HasTypeRT (HasType.str (m := m) (lvl := lvl) (Γ := Γ) (s := s) (ε := ε) (a := a))
  | bin {lvl Γ b ε a} :
      HasTypeRT (HasType.bin (m := m) (lvl := lvl) (Γ := Γ) (b := b) (ε := ε) (a := a))
  | builtin {lvl Γ id s args ε a} (hs : Builtins.scheme id = some s)
      (hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level) :
      HasTypeRT (HasType.builtin (lvl := lvl) (Γ := Γ) (args := args) (ε := ε) (a := a) hs)
  | tail {lvl Γ elem ε a} :
      HasTypeRT (HasType.tail (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | cons {lvl Γ elem ε a} :
      HasTypeRT (HasType.cons (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | tag {lvl Γ l elem tail ε a} :
      HasTypeRT (HasType.tag (m := m) (lvl := lvl) (Γ := Γ) (l := l) (elem := elem)
        (tail := tail) (ε := ε) (a := a))
  | nocases {lvl Γ ret ε a} :
      HasTypeRT (HasType.nocases (m := m) (lvl := lvl) (Γ := Γ) (ret := ret) (ε := ε)
        (a := a))
  | case_ {lvl Γ l inner eff ret tail ε a} :
      HasTypeRT (HasType.case_ (m := m) (lvl := lvl) (Γ := Γ) (l := l) (inner := inner)
        (eff := eff) (ret := ret) (tail := tail) (ε := ε) (a := a))
  | select {lvl Γ l fieldTy tail ε a} :
      HasTypeRT (HasType.select (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (tail := tail) (ε := ε) (a := a))
  | extend {lvl Γ l fieldTy row ε a} :
      HasTypeRT (HasType.extend (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (row := row) (ε := ε) (a := a))
  | overwrite {lvl Γ l newTy oldTy tail ε a} :
      HasTypeRT (HasType.overwrite (m := m) (lvl := lvl) (Γ := Γ) (l := l) (newTy := newTy)
        (oldTy := oldTy) (tail := tail) (ε := ε) (a := a))
  | empty {lvl Γ ε a} :
      HasTypeRT (HasType.empty (m := m) (lvl := lvl) (Γ := Γ) (ε := ε) (a := a))
  | perform {lvl Γ l aa b μ ε ann} :
      HasTypeRT (HasType.perform (m := m) (lvl := lvl) (Γ := Γ) (l := l) (a := aa) (b := b)
        (μ := μ) (ε := ε) (ann := ann))
  | handle {lvl Γ l lift reply tail ret ε ann} :
      HasTypeRT (HasType.handle (m := m) (lvl := lvl) (Γ := Γ) (l := l) (lift := lift)
        (reply := reply) (tail := tail) (ret := ret) (ε := ε) (ann := ann))
  | conv {lvl Γ e τ τ' ε ε'} {h : HasType lvl Γ e τ ε}
      (hτ : Ty.TyEquiv τ τ') (hε : Ty.TyEquiv ε ε') :
      HasTypeRT h → HasTypeRT (HasType.conv h hτ hε)

/-! ## The level-`ℓ`-aware strengthening `HasTypeRTAt ℓ` (gap 1: closure-body re-typing)

`HasTypeRT` bounds a control's `var`/`builtin` instantiation args' levels by `{0, s.level}`. At a
closure application the new control is the closure **body**, which — for a legitimately-typed nested
polymorphic program (e.g. `\w. a w` with `a : ∀α. α→α` used at `[.var 2 0]`) — carries args at the
*inner generalization level* `ℓ` (here `2`), NOT yet ground. Such a body is re-typed by the poly-let
keystone via `substAt ℓ (ground σ)`, which grounds those `ℓ`-tagged args (`[.var 2 0] ↦ [W]`),
recovering `HasTypeRT` of the re-typed derivation.

`HasTypeRTAt ℓ h` is the precondition that re-typing needs: it is exactly `HasTypeRT`, but its
`var`/`builtin` arms bound args by `{0, ℓ, s.level}` (one extra `ℓ` disjunct). `hasTypeRT_subst` then
consumes it and — under a ground `σ` — produces `HasTypeRT` of the re-typed derivation (the `ℓ`
disjunct is discharged: `substAt ℓ σ` removes `ℓ` and introduces only `0`, per
`Ty.not_mem_levels_substAt`/`Ty.mem_levels_substAt_strong`). Like `HasTypeRT`, it does **not** recurse
into `lam`/`let_poly` bodies (they become controls only on their own closure application, re-typed
freshly). -/
inductive HasTypeRTAt {m : Type} (ℓ : Nat) :
    {lvl : Nat} → {Γ : Ctx} → {e : Tree.Node m} → {τ ε : Ty} →
    HasType lvl Γ e τ ε → Prop where
  | var {lvl Γ x s args ε a} (hl : Γ.lookup x = some s)
      (hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = ℓ ∨ l = s.level) :
      HasTypeRTAt ℓ (HasType.var (lvl := lvl) (Γ := Γ) (x := x) (s := s) (args := args)
        (ε := ε) (a := a) hl)
  | lam {lvl lvl' Γ x body argTy εb retTy ε a}
      (hle : lvl ≤ lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono argTy) :: Γ) body retTy εb} :
      HasTypeRTAt ℓ (HasType.lam (ε := ε) (a := a) hle hfv hbody)
  | app {lvl Γ f arg argTy εf retTy ε a}
      {hf : HasType lvl Γ f (.fun argTy εf retTy) ε} {hw : Ty.EffWeaken εf ε}
      {harg : HasType lvl Γ arg argTy ε} :
      HasTypeRTAt ℓ hf → HasTypeRTAt ℓ harg → HasTypeRTAt ℓ (HasType.app (a := a) hf hw harg)
  | let_ {lvl lvl' Γ x defn body defnTy bodyTy ε a}
      {hdefn : HasType lvl Γ defn defnTy ε} (hle : lvl ≤ lvl')
      (hfv : ∀ l ∈ defnTy.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono defnTy) :: Γ) body bodyTy ε} :
      HasTypeRTAt ℓ hdefn → HasTypeRTAt ℓ hbody →
      HasTypeRTAt ℓ (HasType.let_ (a := a) hdefn hle hfv hbody)
  | let_poly {lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a}
      (hstrict : lvl < lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      {hbodydefn : HasType lvl' ((lx, .mono argTy) :: Γ) lbody retTy εb} {hcw : CtxWfV lvl Γ}
      {hbody : HasType (lvl + 1) ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body bodyTy ε} :
      HasTypeRTAt ℓ hbody →
      HasTypeRTAt ℓ (HasType.let_poly (a := a) (la := la) hstrict hfv hbodydefn hcw hbody)
  | int {lvl Γ n ε a} :
      HasTypeRTAt ℓ (HasType.int (m := m) (lvl := lvl) (Γ := Γ) (n := n) (ε := ε) (a := a))
  | str {lvl Γ s ε a} :
      HasTypeRTAt ℓ (HasType.str (m := m) (lvl := lvl) (Γ := Γ) (s := s) (ε := ε) (a := a))
  | bin {lvl Γ b ε a} :
      HasTypeRTAt ℓ (HasType.bin (m := m) (lvl := lvl) (Γ := Γ) (b := b) (ε := ε) (a := a))
  | builtin {lvl Γ id s args ε a} (hs : Builtins.scheme id = some s)
      (hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = ℓ ∨ l = s.level) :
      HasTypeRTAt ℓ (HasType.builtin (lvl := lvl) (Γ := Γ) (args := args) (ε := ε) (a := a) hs)
  | tail {lvl Γ elem ε a} :
      HasTypeRTAt ℓ (HasType.tail (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | cons {lvl Γ elem ε a} :
      HasTypeRTAt ℓ (HasType.cons (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | tag {lvl Γ l elem tail ε a} :
      HasTypeRTAt ℓ (HasType.tag (m := m) (lvl := lvl) (Γ := Γ) (l := l) (elem := elem)
        (tail := tail) (ε := ε) (a := a))
  | nocases {lvl Γ ret ε a} :
      HasTypeRTAt ℓ (HasType.nocases (m := m) (lvl := lvl) (Γ := Γ) (ret := ret) (ε := ε)
        (a := a))
  | case_ {lvl Γ l inner eff ret tail ε a} :
      HasTypeRTAt ℓ (HasType.case_ (m := m) (lvl := lvl) (Γ := Γ) (l := l) (inner := inner)
        (eff := eff) (ret := ret) (tail := tail) (ε := ε) (a := a))
  | select {lvl Γ l fieldTy tail ε a} :
      HasTypeRTAt ℓ (HasType.select (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (tail := tail) (ε := ε) (a := a))
  | extend {lvl Γ l fieldTy row ε a} :
      HasTypeRTAt ℓ (HasType.extend (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (row := row) (ε := ε) (a := a))
  | overwrite {lvl Γ l newTy oldTy tail ε a} :
      HasTypeRTAt ℓ (HasType.overwrite (m := m) (lvl := lvl) (Γ := Γ) (l := l) (newTy := newTy)
        (oldTy := oldTy) (tail := tail) (ε := ε) (a := a))
  | empty {lvl Γ ε a} :
      HasTypeRTAt ℓ (HasType.empty (m := m) (lvl := lvl) (Γ := Γ) (ε := ε) (a := a))
  | perform {lvl Γ l aa b μ ε ann} :
      HasTypeRTAt ℓ (HasType.perform (m := m) (lvl := lvl) (Γ := Γ) (l := l) (a := aa) (b := b)
        (μ := μ) (ε := ε) (ann := ann))
  | handle {lvl Γ l lift reply tail ret ε ann} :
      HasTypeRTAt ℓ (HasType.handle (m := m) (lvl := lvl) (Γ := Γ) (l := l) (lift := lift)
        (reply := reply) (tail := tail) (ret := ret) (ε := ε) (ann := ann))
  | conv {lvl Γ e τ τ' ε ε'} {h : HasType lvl Γ e τ ε}
      (hτ : Ty.TyEquiv τ τ') (hε : Ty.TyEquiv ε ε') :
      HasTypeRTAt ℓ h → HasTypeRTAt ℓ (HasType.conv h hτ hε)

/-! ## The self-contained re-typing precondition `RTSubstReady ℓ` + `hasTypeRT_subst` (gap 1)

`hasTypeRT_subst` must, in one pass, (a) re-type a derivation under `substAt ℓ (ground σ)` — the
`NoGenAt`-driven induction of `hasType_substAt_le` — AND (b) track the `HasTypeRTAt` args bound so the
output is `HasTypeRT`. Mixing an induction on one derivation-indexed `Prop` predicate with an inversion
of the other fails in Lean's dependent elimination (`HasType : Prop` gives no constructor discrimination
through the derivation index; node-based inversion returns mismatched existentials + an irreducible
`let_`/`let_poly` disjunct). `RTSubstReady ℓ h` sidesteps this: it merges both into ONE inductive,
carrying — in a SINGLE recursion — the `var`/`builtin` args bound (`{0, ℓ, s.level}`) AND, at the two
positions the RT recursion does NOT descend into but the re-typing DOES (`lam` body, `let_poly` defn),
the `NoGenAt ℓ` witness that body needs. Inducting on it yields every sub-witness as an arm variable —
no inversion, no existential mismatch, no dead disjunct. The carried `NoGenAt` fields are dischargeable
for free at the (few) construction sites via `noGenAt_of_lt` (whenever `ℓ <` the sub-level) plus, at the
non-strict `ℓ = lvl` boundary, the keystone's `inv_let`-supplied `NoGenAt lvl hdefn`. -/
inductive RTSubstReady {m : Type} (ℓ : Nat) :
    {lvl : Nat} → {Γ : Ctx} → {e : Tree.Node m} → {τ ε : Ty} →
    HasType lvl Γ e τ ε → Prop where
  | var {lvl Γ x s args ε a} (hl : Γ.lookup x = some s)
      (hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = ℓ ∨ l = s.level) :
      RTSubstReady ℓ (HasType.var (lvl := lvl) (Γ := Γ) (x := x) (s := s) (args := args)
        (ε := ε) (a := a) hl)
  | lam {lvl lvl' Γ x body argTy εb retTy ε a}
      (hle : lvl ≤ lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono argTy) :: Γ) body retTy εb} :
      NoGenAt ℓ hbody → RTSubstReady ℓ (HasType.lam (ε := ε) (a := a) hle hfv hbody)
  | app {lvl Γ f arg argTy εf retTy ε a}
      {hf : HasType lvl Γ f (.fun argTy εf retTy) ε} {hw : Ty.EffWeaken εf ε}
      {harg : HasType lvl Γ arg argTy ε} :
      RTSubstReady ℓ hf → RTSubstReady ℓ harg → RTSubstReady ℓ (HasType.app (a := a) hf hw harg)
  | let_ {lvl lvl' Γ x defn body defnTy bodyTy ε a}
      {hdefn : HasType lvl Γ defn defnTy ε} (hle : lvl ≤ lvl')
      (hfv : ∀ l ∈ defnTy.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono defnTy) :: Γ) body bodyTy ε} :
      RTSubstReady ℓ hdefn → RTSubstReady ℓ hbody →
      RTSubstReady ℓ (HasType.let_ (a := a) hdefn hle hfv hbody)
  | let_poly {lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a}
      (hstrict : lvl < lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      {hbodydefn : HasType lvl' ((lx, .mono argTy) :: Γ) lbody retTy εb} {hcw : CtxWfV lvl Γ}
      {hbody : HasType (lvl + 1) ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body bodyTy ε} :
      lvl ≠ ℓ → NoGenAt ℓ hbodydefn → RTSubstReady ℓ hbody →
      RTSubstReady ℓ (HasType.let_poly (a := a) (la := la) hstrict hfv hbodydefn hcw hbody)
  | int {lvl Γ n ε a} :
      RTSubstReady ℓ (HasType.int (m := m) (lvl := lvl) (Γ := Γ) (n := n) (ε := ε) (a := a))
  | str {lvl Γ s ε a} :
      RTSubstReady ℓ (HasType.str (m := m) (lvl := lvl) (Γ := Γ) (s := s) (ε := ε) (a := a))
  | bin {lvl Γ b ε a} :
      RTSubstReady ℓ (HasType.bin (m := m) (lvl := lvl) (Γ := Γ) (b := b) (ε := ε) (a := a))
  | builtin {lvl Γ id s args ε a} (hs : Builtins.scheme id = some s)
      (hargs : ∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = ℓ ∨ l = s.level) :
      RTSubstReady ℓ (HasType.builtin (lvl := lvl) (Γ := Γ) (args := args) (ε := ε) (a := a) hs)
  | tail {lvl Γ elem ε a} :
      RTSubstReady ℓ (HasType.tail (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | cons {lvl Γ elem ε a} :
      RTSubstReady ℓ (HasType.cons (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | tag {lvl Γ l elem tail ε a} :
      RTSubstReady ℓ (HasType.tag (m := m) (lvl := lvl) (Γ := Γ) (l := l) (elem := elem)
        (tail := tail) (ε := ε) (a := a))
  | nocases {lvl Γ ret ε a} :
      RTSubstReady ℓ (HasType.nocases (m := m) (lvl := lvl) (Γ := Γ) (ret := ret) (ε := ε)
        (a := a))
  | case_ {lvl Γ l inner eff ret tail ε a} :
      RTSubstReady ℓ (HasType.case_ (m := m) (lvl := lvl) (Γ := Γ) (l := l) (inner := inner)
        (eff := eff) (ret := ret) (tail := tail) (ε := ε) (a := a))
  | select {lvl Γ l fieldTy tail ε a} :
      RTSubstReady ℓ (HasType.select (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (tail := tail) (ε := ε) (a := a))
  | extend {lvl Γ l fieldTy row ε a} :
      RTSubstReady ℓ (HasType.extend (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (row := row) (ε := ε) (a := a))
  | overwrite {lvl Γ l newTy oldTy tail ε a} :
      RTSubstReady ℓ (HasType.overwrite (m := m) (lvl := lvl) (Γ := Γ) (l := l) (newTy := newTy)
        (oldTy := oldTy) (tail := tail) (ε := ε) (a := a))
  | empty {lvl Γ ε a} :
      RTSubstReady ℓ (HasType.empty (m := m) (lvl := lvl) (Γ := Γ) (ε := ε) (a := a))
  | perform {lvl Γ l aa b μ ε ann} :
      RTSubstReady ℓ (HasType.perform (m := m) (lvl := lvl) (Γ := Γ) (l := l) (a := aa) (b := b)
        (μ := μ) (ε := ε) (ann := ann))
  | handle {lvl Γ l lift reply tail ret ε ann} :
      RTSubstReady ℓ (HasType.handle (m := m) (lvl := lvl) (Γ := Γ) (l := l) (lift := lift)
        (reply := reply) (tail := tail) (ret := ret) (ε := ε) (ann := ann))
  | conv {lvl Γ e τ τ' ε ε'} {h : HasType lvl Γ e τ ε}
      (hτ : Ty.TyEquiv τ τ') (hε : Ty.TyEquiv ε ε') :
      RTSubstReady ℓ h → RTSubstReady ℓ (HasType.conv h hτ hε)

/-- **The RT-tracking companion to `hasType_substAt_le` (gap 1: closure-body re-typing).** From a
`RTSubstReady ℓ h` (the level-`ℓ`-aware bound + carried `NoGenAt` witnesses) and a **ground** `σ`,
produces a bundled re-typed derivation `h'` **together with** `HasTypeRT h'`. Single induction on
`RTSubstReady`; every sub-witness is an arm variable. The `var`/`builtin` arms discharge the extra `ℓ`
disjunct of the input args bound (`substAt ℓ σ` removes `ℓ` via `Ty.not_mem_levels_substAt`, introduces
only `0` via `hσ`, so the output lands in `{0, s.level}`). The `lam`/`let_poly`-defn bodies are re-typed
via `hasType_substAt_le` using the carried `NoGenAt`; RT-recursive positions use the IH. -/
theorem hasTypeRT_subst {ℓ : Nat} (hℓ : ℓ ≠ 0) (σ : Nat → Ty)
    (hσ : ∀ i, ∀ l ∈ (σ i).levels, l = 0)
    {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    {h : HasType lvl Γ e τ ε} (hr : RTSubstReady ℓ h) (hlt : ℓ ≤ lvl)
    (hΓ : PolyAboveFV ℓ Γ e) :
    ∃ h' : HasType lvl (substCtxAt ℓ σ Γ) e (Ty.substAt ℓ σ τ) (Ty.substAt ℓ σ ε), HasTypeRT h' := by
  have hσle : ∀ i, ∀ l ∈ (σ i).levels, l = 0 ∨ l = ℓ := fun i l hl => Or.inl (hσ i l hl)
  have hσleq : ∀ i, ∀ l ∈ (σ i).levels, l ≤ ℓ := fun i l hl => by rw [hσ i l hl]; exact Nat.zero_le ℓ
  have hσℓ : ∀ i, ℓ ∉ (σ i).levels := fun i hmem => hℓ (hσ i ℓ hmem)
  revert hlt hΓ
  induction hr with
  | @var lvl Γ x s args ε a hl hargs =>
      intro hlt hΓ
      have hdisj : s.arity = 0 ∨ (ℓ ≠ s.level ∧ ∀ i, ∀ j, j ∉ Ty.freeVarsAt s.level (σ i)) := by
        by_cases h0 : s.arity = 0
        · exact Or.inl h0
        · obtain ⟨hlvl0, hlvlℓ⟩ :=
            (hΓ x (by simp [Tree.Node.freeVars]) s hl).resolve_left h0
          refine Or.inr ⟨Ne.symm hlvlℓ, ?_⟩
          intro i j hj
          exact hlvl0 (hσ i s.level (Ty.mem_levels_of_mem_freeVarsAt hj))
      rw [substAt_instantiateV_scheme hdisj args]
      refine ⟨HasType.var (substCtxAt_lookup hl), HasTypeRT.var (substCtxAt_lookup hl) ?_⟩
      intro t ht l hl2
      rw [List.mem_map] at ht; obtain ⟨t0, ht0, rfl⟩ := ht
      have hlℓ : l ≠ ℓ := fun hh => Ty.not_mem_levels_substAt hσℓ t0 (hh ▸ hl2)
      rcases Ty.mem_levels_substAt_strong hl2 with hl' | ⟨_, i, hi⟩
      · rcases hargs t0 ht0 l hl' with h0 | hℓ2 | hsl
        · exact Or.inl h0
        · exact absurd hℓ2 hlℓ
        · exact Or.inr hsl
      · exact Or.inl (hσ i l hi)
  | @builtin lvl Γ id s args ε a hs hargs =>
      intro hlt hΓ
      rw [substAt_instantiateV_closed (by rw [Builtins.scheme_level hs]; exact hℓ)
            (Builtins.scheme_no_level hℓ hs) args,
          Builtins.scheme_substSchemeVAt hℓ σ hs]
      refine ⟨HasType.builtin hs, HasTypeRT.builtin hs ?_⟩
      intro t ht l hl2
      rw [List.mem_map] at ht; obtain ⟨t0, ht0, rfl⟩ := ht
      have hlℓ : l ≠ ℓ := fun hh => Ty.not_mem_levels_substAt hσℓ t0 (hh ▸ hl2)
      rcases Ty.mem_levels_substAt_strong hl2 with hl' | ⟨_, i, hi⟩
      · rcases hargs t0 ht0 l hl' with h0 | hℓ2 | hsl
        · exact Or.inl h0
        · exact absurd hℓ2 hlℓ
        · exact Or.inr hsl
      · exact Or.inl (hσ i l hi)
  | @lam lvl lvl' Γ x body argTy εb retTy ε a hle hfv hbody hng_body =>
      intro hlt hΓ
      have hfv' : ∀ l ∈ (Ty.substAt ℓ σ argTy).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hfv l hl'
        · exact Nat.lt_of_le_of_lt (hσleq i l hi) (hfv ℓ hm)
      have hΓdb : PolyAboveFV ℓ ((x, Scheme.mono argTy) :: Γ) body :=
        polyAboveFV_bind (Or.inl rfl) hΓ
          (fun y hy hne => List.mem_filter.mpr ⟨hy, by simpa using hne⟩)
      have hbody' := hasType_substAt_le hℓ σ hσle hng_body (le_trans hlt hle) hΓdb
      simp only [Ty.substAt]
      exact ⟨HasType.lam hle hfv' hbody', HasTypeRT.lam (hbody := hbody') hle hfv'⟩
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg rf rarg ihf iharg =>
      intro hlt hΓ
      obtain ⟨hf', rf'⟩ := ihf hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy))
      obtain ⟨harg', rarg'⟩ := iharg hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_right _ hy))
      exact ⟨HasType.app hf' (Ty.substAt_effWeaken ℓ σ hw) harg',
        HasTypeRT.app (hw := Ty.substAt_effWeaken ℓ σ hw) rf' rarg'⟩
  | @let_ lvl lvl' Γ x defn body defnTy bodyTy ε a hdefn hle hfv hbody rd rb ihdefn ihbody =>
      intro hlt hΓ
      have hfv' : ∀ l ∈ (Ty.substAt ℓ σ defnTy).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hfv l hl'
        · exact Nat.lt_of_le_of_lt (hσleq i l hi) (hfv ℓ hm)
      obtain ⟨hd, rd'⟩ := ihdefn hlt (polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy))
      obtain ⟨hb, rb'⟩ := ihbody (le_trans hlt hle)
        (polyAboveFV_bind (Or.inl rfl) hΓ
          (fun y hy hne => List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne⟩)))
      exact ⟨HasType.let_ hd hle hfv' hb, HasTypeRT.let_ hle hfv' rd' rb'⟩
  | @let_poly lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a hstrict hfv hbodydefn hcw hbody
      hne hng_defn rb ihbody =>
      intro hlt hΓ
      have hlts : ℓ < lvl := lt_of_le_of_ne hlt (Ne.symm hne)
      have hne' : ℓ ≠ lvl := Nat.ne_of_lt hlts
      have hcleanlvl : ∀ i, lvl ∉ (σ i).levels := fun i hmem => absurd (hσ i lvl hmem) (by omega)
      have hΓdefn : PolyAboveFV ℓ Γ ⟨.Lambda lx lbody, la⟩ :=
        polyAboveFV_sub hΓ (fun y hy => List.mem_append_left _ hy)
      have hΓdb : PolyAboveFV ℓ ((lx, Scheme.mono argTy) :: Γ) lbody :=
        polyAboveFV_bind (Or.inl rfl) hΓdefn
          (fun y hy hne2 => List.mem_filter.mpr ⟨hy, by simpa using hne2⟩)
      have hbd := hasType_substAt_le hℓ σ hσle hng_defn (le_of_lt (lt_trans hlts hstrict)) hΓdb
      have hfv' : ∀ l ∈ (Ty.substAt ℓ σ argTy).levels, l < lvl' := by
        intro l hl
        rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hm, i, hi⟩
        · exact hfv l hl'
        · exact Nat.lt_of_le_of_lt (hσleq i l hi) (hfv ℓ hm)
      have hΓ1 : PolyAboveFV ℓ ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body :=
        polyAboveFV_bind (Or.inr (by simp only [Scheme.genAtV]; omega)) hΓ
          (fun y hy hne2 => List.mem_append_right _ (List.mem_filter.mpr ⟨hy, by simpa using hne2⟩))
      have key : ∃ hb : HasType (lvl + 1)
          (substCtxAt ℓ σ ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ)) body
          (Ty.substAt ℓ σ bodyTy) (Ty.substAt ℓ σ ε), HasTypeRT hb :=
        ihbody (by omega : ℓ ≤ lvl + 1) hΓ1
      rw [substCtxAt_cons_genAtV hne' hcleanlvl] at key
      simp only [Ty.substAt] at key
      obtain ⟨hbodyIH, rbody'⟩ := key
      exact ⟨HasType.let_poly hstrict hfv' hbd (ctxWfV_substCtxAt hlts hσleq hcw) hbodyIH,
        HasTypeRT.let_poly (hbodydefn := hbd) (hcw := ctxWfV_substCtxAt hlts hσleq hcw)
          hstrict hfv' rbody'⟩
  | int => intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.int, HasTypeRT.int⟩
  | str => intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.str, HasTypeRT.str⟩
  | bin => intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.bin, HasTypeRT.bin⟩
  | tail => intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.tail, HasTypeRT.tail⟩
  | cons => intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.cons, HasTypeRT.cons⟩
  | tag => intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.tag, HasTypeRT.tag⟩
  | nocases => intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.nocases, HasTypeRT.nocases⟩
  | case_ => intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.case_, HasTypeRT.case_⟩
  | select => intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.select, HasTypeRT.select⟩
  | extend => intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.extend, HasTypeRT.extend⟩
  | overwrite =>
      intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.overwrite, HasTypeRT.overwrite⟩
  | empty => intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.empty, HasTypeRT.empty⟩
  | perform => intro hlt hΓ; simp only [Ty.substAt]; exact ⟨HasType.perform, HasTypeRT.perform⟩
  | @handle lvl Γ l lift reply tail ret ε a =>
      intro hlt hΓ
      have heq : Ty.substAt ℓ σ (handleTy l lift reply tail ret)
          = handleTy l (Ty.substAt ℓ σ lift) (Ty.substAt ℓ σ reply) (Ty.substAt ℓ σ tail)
              (Ty.substAt ℓ σ ret) := by
        simp [handleTy, handlerTy, execTy, kontTy, Ty.substAt]
      rw [heq]; exact ⟨HasType.handle, HasTypeRT.handle⟩
  | @conv lvl Γ e τ τ' ε ε' h hτ hε rh ih =>
      intro hlt hΓ
      obtain ⟨h', rh'⟩ := ih hlt hΓ
      exact ⟨HasType.conv h' (Ty.substAt_tyEquiv ℓ σ hτ) (Ty.substAt_tyEquiv ℓ σ hε),
        HasTypeRT.conv (Ty.substAt_tyEquiv ℓ σ hτ) (Ty.substAt_tyEquiv ℓ σ hε) rh'⟩

/-- **The var-preservation discharge lemma.** From a `HasTypeRT` control derivation on a bare
variable node, recover the looked-up scheme, its instantiation args, the lookup, the equivalence (as
`inv_var`) **and** the args side-condition needed to apply `envwf_lookup`'s conditional readiness
`hvty`. This is the single fact gap 1 was missing: it replaces `inv_var` at the RT var-preservation
site. -/
theorem inv_var_rt {lvl : Nat} {Γ : Ctx} {x : String} {a : m} {τ ε : Ty}
    {h : HasType lvl Γ (⟨.Variable x, a⟩ : Tree.Node m) τ ε} (hrt : HasTypeRT h) :
    ∃ s args, Γ.lookup x = some s ∧ Ty.TyEquiv (s.instantiateV args) τ ∧
      (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level) := by
  generalize he : (⟨.Variable x, a⟩ : Tree.Node m) = enode at h
  revert he
  induction hrt with
  | @var lvl Γ x' s args ε a hl hargs =>
      intro he; cases he; exact ⟨s, args, hl, .refl _, hargs⟩
  | @conv lvl Γ e τ' τ'' ε' ε'' hh hτ hε rh ih =>
      intro he
      obtain ⟨s, args, hl, heq, hargs⟩ := ih he
      exact ⟨s, args, hl, heq.trans hτ, hargs⟩
  | _ => intro he; exact absurd he (by simp)

/-- **The builtin analog of `inv_var_rt`.** Recovers the builtin scheme, args, the type equivalence
(as `inv_builtin`) and the args side-condition. -/
theorem inv_builtin_rt {lvl : Nat} {Γ : Ctx} {id : String} {a : m} {τ ε : Ty}
    {h : HasType lvl Γ (⟨.Builtin id, a⟩ : Tree.Node m) τ ε} (hrt : HasTypeRT h) :
    ∃ s args, Builtins.scheme id = some s ∧ Ty.TyEquiv (s.instantiateV args) τ ∧
      (∀ t ∈ args, ∀ l ∈ t.levels, l = 0 ∨ l = s.level) := by
  generalize he : (⟨.Builtin id, a⟩ : Tree.Node m) = enode at h
  revert he
  induction hrt with
  | @builtin lvl Γ id' s args ε a hs hargs =>
      intro he; cases he; exact ⟨s, args, hs, .refl _, hargs⟩
  | @conv lvl Γ e τ' τ'' ε' ε'' hh hτ hε rh ih =>
      intro he
      obtain ⟨s, args, hs, heq, hargs⟩ := ih he
      exact ⟨s, args, hs, heq.trans hτ, hargs⟩
  | _ => intro he; exact absurd he (by simp)

/-- **Any lambda-node derivation is `HasTypeRT`.** A lambda control (which becomes a closure) is
always runtime-restricted regardless of its body — `HasTypeRT.lam` carries no body premise. Used at
the lam-control and `let_poly`-defn preservation steps to re-establish RT of the produced
control. -/
theorem hasTypeRT_lambda {lvl : Nat} {Γ : Ctx} {x : String} {body : Tree.Node m} {a : m} {τ ε : Ty}
    (h : HasType lvl Γ (⟨.Lambda x body, a⟩ : Tree.Node m) τ ε) : HasTypeRT h := by
  generalize he : (⟨.Lambda x body, a⟩ : Tree.Node m) = enode at h
  revert he
  induction h with
  | @lam lvl lvl' Γ x' body' argTy εb retTy ε a hle hfv hbody _ =>
      intro he; cases he; exact HasTypeRT.lam (hbody := hbody) hle hfv
  | @conv lvl Γ e τ' τ'' ε' ε'' hh hτ hε ih =>
      intro he; exact HasTypeRT.conv hτ hε (ih he)
  | _ => intro he; exact absurd he (by simp)

/-- **RT-inversion for `Apply`** (the RT analog of `inv_app`): recovers the function/argument
derivations (conv-adjusted, as `inv_app`) **together with** their `HasTypeRT` witnesses. At the
app-preservation step the function becomes the immediate control and the argument is stored in the
`Arg` frame — both need RT re-established, supplied here. -/
theorem inv_app_rt {lvl : Nat} {Γ : Ctx} {f arg : Tree.Node m} {a : m} {τ ε : Ty}
    {h : HasType lvl Γ (⟨.Apply f arg, a⟩ : Tree.Node m) τ ε} (hrt : HasTypeRT h) :
    ∃ argTy εf, ∃ (hf : HasType lvl Γ f (.fun argTy εf τ) ε) (harg : HasType lvl Γ arg argTy ε),
      Ty.EffWeaken εf ε ∧ HasTypeRT hf ∧ HasTypeRT harg := by
  generalize he : (⟨.Apply f arg, a⟩ : Tree.Node m) = enode at h
  revert he
  induction hrt with
  | @app lvl Γ f' arg' argTy εf retTy ε a hf hw harg rf rarg _ _ =>
      intro he; cases he; exact ⟨argTy, εf, hf, harg, hw, rf, rarg⟩
  | @conv lvl Γ e τ' τ'' ε' ε'' hh hτ hε rh ih =>
      intro he
      obtain ⟨argTy, εf, hf, harg, hw, rf, rarg⟩ := ih he
      exact ⟨argTy, εf, HasType.conv hf (.congrFun (.refl _) (.refl _) hτ) hε,
        HasType.conv harg (.refl _) hε, Ty.effWeaken_tyEquiv_right hw hε,
        HasTypeRT.conv (.congrFun (.refl _) (.refl _) hτ) hε rf,
        HasTypeRT.conv (.refl _) hε rarg⟩
  | _ => intro he; exact absurd he (by simp)

/-- **RT-inversion for `Let`** (the RT analog of `inv_let`): the mono branch supplies RT of both the
`defn` (immediate control) and the `body` (stored in the `Assign` frame); the poly branch supplies
RT of the `body` only — the lambda-`defn` control's RT is re-built fresh via `hasTypeRT_lambda`. -/
theorem inv_let_rt {lvl : Nat} {Γ : Ctx} {x : String} {defn body : Tree.Node m} {a : m} {τ ε : Ty}
    {h : HasType lvl Γ (⟨.Let x defn body, a⟩ : Tree.Node m) τ ε} (hrt : HasTypeRT h) :
    (∃ lvl' defnTy, ∃ (hdefn : HasType lvl Γ defn defnTy ε)
        (hbody : HasType lvl' ((x, .mono defnTy) :: Γ) body τ ε),
        lvl ≤ lvl' ∧ (∀ l ∈ defnTy.levels, l < lvl') ∧ HasTypeRT hdefn ∧ HasTypeRT hbody) ∨
    (∃ lx lbody la defnTy, ∃ (_ : defn = ⟨.Lambda lx lbody, la⟩)
        (hdefn : HasType lvl Γ defn defnTy ε) (_ : CtxWfV lvl Γ)
        (hbody : HasType (lvl + 1) ((x, Scheme.genAtV lvl defnTy) :: Γ) body τ ε),
        NoGenAt lvl hdefn ∧ HasTypeRT hbody) := by
  generalize he : (⟨.Let x defn body, a⟩ : Tree.Node m) = enode at h
  revert he
  induction hrt with
  | @let_ lvl lvl' Γ x' defn' body' defnTy bodyTy ε a hdefn hle hfv hbody rd rb _ _ =>
      intro he; cases he
      exact Or.inl ⟨lvl', defnTy, hdefn, hbody, hle, hfv, rd, rb⟩
  | @let_poly lvl lvl' Γ x' lx lbody la body' argTy εb retTy bodyTy ε a hstrict hfv hbodydefn hcw
      hbody rb _ =>
      intro he; cases he
      exact Or.inr ⟨lx, lbody, la, .fun argTy εb retTy, rfl,
        HasType.letpoly_defn hstrict hfv hbodydefn, hcw, hbody,
        noGenAt_letpoly_defn hstrict hfv hbodydefn, rb⟩
  | @conv lvl Γ e τ' τ'' ε' ε'' hh hτ hε rh ih =>
      intro he
      rcases ih he with ⟨lvl', defnTy, hdefn, hbody, hle, hfv, rd, rb⟩ |
          ⟨lx, lbody, la, defnTy, hdl, hdefn, hcw, hbody, hng, rb⟩
      · exact Or.inl ⟨lvl', defnTy, HasType.conv hdefn (.refl _) hε, HasType.conv hbody hτ hε,
          hle, hfv, HasTypeRT.conv (.refl _) hε rd, HasTypeRT.conv hτ hε rb⟩
      · exact Or.inr ⟨lx, lbody, la, defnTy, hdl, HasType.conv hdefn (.refl _) hε, hcw,
          HasType.conv hbody hτ hε, NoGenAt.conv (.refl _) hε hng, HasTypeRT.conv hτ hε rb⟩
  | _ => intro he; exact absurd he (by simp)

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
  | @let_poly lvl lvl' Γ₁ z lx lbody la body argTy εb retTy bodyTy ε' a hstrict hfv hbodydefn hcw
      hbody ihdefn ihbody =>
      intro Δ Γ x σ σ' heq hc; subst heq
      exact HasType.let_poly hstrict hfv
        (ihdefn ((lx, Scheme.mono argTy) :: Δ) Γ x σ σ' rfl hc) (ctxWfV_ctxConv hc hcw)
        (ihbody ((z, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Δ) Γ x σ σ' rfl hc)
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

/-- **RT-indexed context-binding conversion** (the `HasTypeRT` companion to `hasType_ctxConv`).
Since `HasTypeRT` is indexed by the *specific* `HasType` derivation and `hasType_ctxConv`'s output is
opaque (a recursor application that case-splits on the runtime binder lookup), we cannot state the RT
of `hasType_ctxConv h …` directly. Instead we bundle: from `HasTypeRT h` we rebuild — mirroring
`hasType_ctxConv` arm-for-arm — a fresh converted derivation `h'` **together with** its `HasTypeRT`
witness. `stackSeg_input_conv` destructures both. The `lam`/`let_poly` defn subterms reuse the plain
`hasType_ctxConv` (their RT is not required by `HasTypeRT.lam`/`.let_poly`). -/
theorem hasTypeRT_ctxConv {m : Type} {lvl : Nat} {Γ₀ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    {h : HasType lvl Γ₀ e τ ε} (hrt : HasTypeRT h) :
    ∀ (Δ Γ : Ctx) (x : String) (σ σ' : Ty),
      Γ₀ = Δ ++ (x, .mono σ) :: Γ → Ty.TyEquiv σ' σ →
      ∃ h' : HasType lvl (Δ ++ (x, .mono σ') :: Γ) e τ ε, HasTypeRT h' := by
  induction hrt with
  | @var lvl Γ₁ y s args ε' a hl hargs =>
      intro Δ Γ x σ σ' heq hc; subst heq
      rw [List.lookup_append] at hl
      cases hΔ : Δ.lookup y with
      | some v =>
          rw [hΔ, Option.some_or] at hl; cases hl
          exact ⟨HasType.var (by rw [List.lookup_append, hΔ, Option.some_or]),
            HasTypeRT.var (by rw [List.lookup_append, hΔ, Option.some_or]) hargs⟩
      | none =>
          rw [hΔ, Option.none_or] at hl
          by_cases hyx : (y == x) = true
          · simp only [List.lookup_cons, hyx] at hl; cases hl
            refine ⟨HasType.conv
              (HasType.var (s := .mono σ') (args := args)
                (by simp only [List.lookup_append, hΔ, Option.none_or, List.lookup_cons, hyx]))
              ?_ (.refl _), HasTypeRT.conv ?_ (.refl _)
                (HasTypeRT.var (s := .mono σ') (args := args)
                  (by simp only [List.lookup_append, hΔ, Option.none_or, List.lookup_cons, hyx])
                  hargs)⟩
            · simp only [Scheme.instantiateV_mono]; exact hc
            · simp only [Scheme.instantiateV_mono]; exact hc
          · simp only [List.lookup_cons, hyx, Bool.false_eq_true] at hl ⊢
            exact ⟨HasType.var (s := s) (args := args)
                (by simp only [List.lookup_append, hΔ, Option.none_or, List.lookup_cons, hyx,
                  Bool.false_eq_true]; exact hl),
              HasTypeRT.var (s := s) (args := args)
                (by simp only [List.lookup_append, hΔ, Option.none_or, List.lookup_cons, hyx,
                  Bool.false_eq_true]; exact hl) hargs⟩
  | @lam lvl lvl' Γ₁ z body argTy εb retTy ε' a hle hfv hbody =>
      intro Δ Γ x σ σ' heq hc; subst heq
      have hb := hasType_ctxConv hbody ((z, .mono argTy) :: Δ) Γ x σ σ' rfl hc
      exact ⟨HasType.lam hle hfv hb, HasTypeRT.lam (hbody := hb) hle hfv⟩
  | @app lvl Γ₁ f arg argTy εf retTy ε' a hf hw harg rf rarg ihf iharg =>
      intro Δ Γ x σ σ' heq hc; subst heq
      obtain ⟨hf', rf'⟩ := ihf Δ Γ x σ σ' rfl hc
      obtain ⟨harg', rarg'⟩ := iharg Δ Γ x σ σ' rfl hc
      exact ⟨HasType.app hf' hw harg', HasTypeRT.app (hw := hw) rf' rarg'⟩
  | @let_ lvl lvl' Γ₁ z defn body defnTy bodyTy ε' a hdefn hle hfv hbody rd rb ihd ihb =>
      intro Δ Γ x σ σ' heq hc; subst heq
      obtain ⟨hd', rd'⟩ := ihd Δ Γ x σ σ' rfl hc
      obtain ⟨hb', rb'⟩ := ihb ((z, .mono defnTy) :: Δ) Γ x σ σ' rfl hc
      exact ⟨HasType.let_ hd' hle hfv hb', HasTypeRT.let_ hle hfv rd' rb'⟩
  | @let_poly lvl lvl' Γ₁ z lx lbody la body argTy εb retTy bodyTy ε' a hstrict hfv hbodydefn hcw
      hbody rb ihb =>
      intro Δ Γ x σ σ' heq hc; subst heq
      obtain ⟨hb', rb'⟩ := ihb ((z, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Δ) Γ x σ σ' rfl hc
      have hbd' := hasType_ctxConv hbodydefn ((lx, Scheme.mono argTy) :: Δ) Γ x σ σ' rfl hc
      have hcw' := ctxWfV_ctxConv hc hcw
      exact ⟨HasType.let_poly hstrict hfv hbd' hcw' hb',
        HasTypeRT.let_poly hstrict hfv (hbodydefn := hbd') (hcw := hcw') rb'⟩
  | int => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.int, HasTypeRT.int⟩
  | str => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.str, HasTypeRT.str⟩
  | bin => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.bin, HasTypeRT.bin⟩
  | builtin hs hargs =>
      intro Δ Γ x σ σ' heq hc; subst heq
      exact ⟨HasType.builtin hs, HasTypeRT.builtin hs hargs⟩
  | tail => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.tail, HasTypeRT.tail⟩
  | cons => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.cons, HasTypeRT.cons⟩
  | tag => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.tag, HasTypeRT.tag⟩
  | nocases =>
      intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.nocases, HasTypeRT.nocases⟩
  | case_ => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.case_, HasTypeRT.case_⟩
  | select => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.select, HasTypeRT.select⟩
  | extend => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.extend, HasTypeRT.extend⟩
  | overwrite =>
      intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.overwrite, HasTypeRT.overwrite⟩
  | empty => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.empty, HasTypeRT.empty⟩
  | perform =>
      intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.perform, HasTypeRT.perform⟩
  | handle => intro Δ Γ x σ σ' heq hc; subst heq; exact ⟨HasType.handle, HasTypeRT.handle⟩
  | @conv lvl Γ₁ e' τ' τ'' ε₁ ε₂ hh hτ hε rh ih =>
      intro Δ Γ x σ σ' heq hc; subst heq
      obtain ⟨h'', rh''⟩ := ih Δ Γ x σ σ' rfl hc
      exact ⟨HasType.conv h'' hτ hε, HasTypeRT.conv hτ hε rh''⟩

/-- The head-binding (`Δ = []`) specialization of `hasTypeRT_ctxConv`, the form `stackSeg_input_conv`
uses: from a stored assign-body's `HasTypeRT` witness, rebuild both the type-converted body
derivation and its RT witness when the bound variable's type is rewritten along a `TyEquiv`. -/
theorem hasTypeRT_ctxHead_conv {m : Type} {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {x : String}
    {σ σ' τ ε : Ty} {h : HasType lvl ((x, .mono σ) :: Γ) e τ ε} (hrt : HasTypeRT h)
    (hc : Ty.TyEquiv σ' σ) :
    ∃ h' : HasType lvl ((x, .mono σ') :: Γ) e τ ε, HasTypeRT h' :=
  hasTypeRT_ctxConv hrt [] Γ x σ σ' rfl hc

/-! ## Global level cap `LevelsBelow` (freshness discipline for the generalization-level raise)

The generalization-level *raise* (`hasType_raise`, below/next session) relabels every reachable
`let_poly`'s stored generalization level `k ↦ k + o` and must pick the target genuinely **fresh**
w.r.t. that node's own `defnTy` (`k + o ∉ defnTy.levels`, so the relabel does not inflate `genAtV`'s
arity — Session G9 Finding 2(b)). A single uniform offset `o ≥ N`, with `N` a strict upper bound on
every `let_poly`-`defnTy` level anywhere in the derivation, discharges this uniformly. `LevelsBelow N h`
is that bound as a `NoGenAt`-shaped inductive (indexed by the derivation): its `let_poly` arm records
`∀ l ∈ defnTy.levels, l < N` and every arm recurses; `exists_levelsBelow` supplies some `N` for any
derivation (finite syntax ⇒ finitely many levels ⇒ take the max). -/

/-- **Every reachable `let_poly`'s `defnTy` has all its levels `< N`** (a parallel-to-`HasType`
predicate, indexed by the derivation, mirroring `NoGenAt`). Only the `let_poly` arm carries a
non-trivial bound (`∀ l ∈ defnTy.levels, l < N`); every constructor recurses on its
sub-derivation(s). Consumed by `hasType_raise` to pick a fresh relabel target `k + o` with
`o ≥ N`. -/
inductive LevelsBelow {m : Type} (N : Nat) :
    {lvl : Nat} → {Γ : Ctx} → {e : Tree.Node m} → {τ ε : Ty} →
    HasType lvl Γ e τ ε → Prop where
  | var {lvl Γ x s args ε a} (hl : Γ.lookup x = some s) :
      LevelsBelow N (HasType.var (lvl := lvl) (Γ := Γ) (x := x) (s := s) (args := args)
        (ε := ε) (a := a) hl)
  | lam {lvl lvl' Γ x body argTy εb retTy ε a}
      (hle : lvl ≤ lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono argTy) :: Γ) body retTy εb} :
      LevelsBelow N hbody → LevelsBelow N (HasType.lam (ε := ε) (a := a) hle hfv hbody)
  | app {lvl Γ f arg argTy εf retTy ε a}
      {hf : HasType lvl Γ f (.fun argTy εf retTy) ε} {hw : Ty.EffWeaken εf ε}
      {harg : HasType lvl Γ arg argTy ε} :
      LevelsBelow N hf → LevelsBelow N harg → LevelsBelow N (HasType.app (a := a) hf hw harg)
  | let_ {lvl lvl' Γ x defn body defnTy bodyTy ε a}
      {hdefn : HasType lvl Γ defn defnTy ε} (hle : lvl ≤ lvl')
      (hfv : ∀ l ∈ defnTy.levels, l < lvl')
      {hbody : HasType lvl' ((x, .mono defnTy) :: Γ) body bodyTy ε} :
      LevelsBelow N hdefn → LevelsBelow N hbody →
      LevelsBelow N (HasType.let_ (a := a) hdefn hle hfv hbody)
  | let_poly {lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a}
      (hstrict : lvl < lvl') (hfv : ∀ l ∈ argTy.levels, l < lvl')
      {hbodydefn : HasType lvl' ((lx, .mono argTy) :: Γ) lbody retTy εb} {hcw : CtxWfV lvl Γ}
      {hbody : HasType (lvl + 1) ((x, Scheme.genAtV lvl (.fun argTy εb retTy)) :: Γ) body bodyTy ε} :
      (∀ l ∈ (Ty.fun argTy εb retTy).levels, l < N) → LevelsBelow N hbodydefn → LevelsBelow N hbody →
      LevelsBelow N (HasType.let_poly (a := a) (la := la) hstrict hfv hbodydefn hcw hbody)
  | int {lvl Γ n ε a} :
      LevelsBelow N (HasType.int (m := m) (lvl := lvl) (Γ := Γ) (n := n) (ε := ε) (a := a))
  | str {lvl Γ s ε a} :
      LevelsBelow N (HasType.str (m := m) (lvl := lvl) (Γ := Γ) (s := s) (ε := ε) (a := a))
  | bin {lvl Γ b ε a} :
      LevelsBelow N (HasType.bin (m := m) (lvl := lvl) (Γ := Γ) (b := b) (ε := ε) (a := a))
  | builtin {lvl Γ id s args ε a} (hs : Builtins.scheme id = some s) :
      LevelsBelow N (HasType.builtin (lvl := lvl) (Γ := Γ) (args := args) (ε := ε) (a := a) hs)
  | tail {lvl Γ elem ε a} :
      LevelsBelow N (HasType.tail (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | cons {lvl Γ elem ε a} :
      LevelsBelow N (HasType.cons (m := m) (lvl := lvl) (Γ := Γ) (elem := elem) (ε := ε) (a := a))
  | tag {lvl Γ l elem tail ε a} :
      LevelsBelow N (HasType.tag (m := m) (lvl := lvl) (Γ := Γ) (l := l) (elem := elem)
        (tail := tail) (ε := ε) (a := a))
  | nocases {lvl Γ ret ε a} :
      LevelsBelow N (HasType.nocases (m := m) (lvl := lvl) (Γ := Γ) (ret := ret) (ε := ε)
        (a := a))
  | case_ {lvl Γ l inner eff ret tail ε a} :
      LevelsBelow N (HasType.case_ (m := m) (lvl := lvl) (Γ := Γ) (l := l) (inner := inner)
        (eff := eff) (ret := ret) (tail := tail) (ε := ε) (a := a))
  | select {lvl Γ l fieldTy tail ε a} :
      LevelsBelow N (HasType.select (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (tail := tail) (ε := ε) (a := a))
  | extend {lvl Γ l fieldTy row ε a} :
      LevelsBelow N (HasType.extend (m := m) (lvl := lvl) (Γ := Γ) (l := l) (fieldTy := fieldTy)
        (row := row) (ε := ε) (a := a))
  | overwrite {lvl Γ l newTy oldTy tail ε a} :
      LevelsBelow N (HasType.overwrite (m := m) (lvl := lvl) (Γ := Γ) (l := l) (newTy := newTy)
        (oldTy := oldTy) (tail := tail) (ε := ε) (a := a))
  | empty {lvl Γ ε a} :
      LevelsBelow N (HasType.empty (m := m) (lvl := lvl) (Γ := Γ) (ε := ε) (a := a))
  | perform {lvl Γ l aa b μ ε ann} :
      LevelsBelow N (HasType.perform (m := m) (lvl := lvl) (Γ := Γ) (l := l) (a := aa) (b := b)
        (μ := μ) (ε := ε) (ann := ann))
  | handle {lvl Γ l lift reply tail ret ε ann} :
      LevelsBelow N (HasType.handle (m := m) (lvl := lvl) (Γ := Γ) (l := l) (lift := lift)
        (reply := reply) (tail := tail) (ret := ret) (ε := ε) (ann := ann))
  | conv {lvl Γ e τ τ' ε ε'} {h : HasType lvl Γ e τ ε}
      (hτ : Ty.TyEquiv τ τ') (hε : Ty.TyEquiv ε ε') :
      LevelsBelow N h → LevelsBelow N (HasType.conv h hτ hε)

/-- **Monotonicity of the global level cap.** A derivation bounded by `N` is bounded by any `N' ≥ N`. -/
theorem LevelsBelow.mono {m : Type} {N N' : Nat} (hle : N ≤ N')
    {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty} {h : HasType lvl Γ e τ ε}
    (hlb : LevelsBelow N h) : LevelsBelow N' h := by
  induction hlb with
  | var hl => exact LevelsBelow.var hl
  | lam hle' hfv _ ih => exact LevelsBelow.lam hle' hfv ih
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg _ _ ihf iharg =>
      exact LevelsBelow.app (hw := hw) ihf iharg
  | let_ hle' hfv _ _ ihd ihb => exact LevelsBelow.let_ hle' hfv ihd ihb
  | @let_poly lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a hstrict hfv hbodydefn hcw hbody
      hbnd _ _ ihd ihb =>
      exact LevelsBelow.let_poly (hcw := hcw) hstrict hfv
        (fun l hl => lt_of_lt_of_le (hbnd l hl) hle) ihd ihb
  | int => exact LevelsBelow.int
  | str => exact LevelsBelow.str
  | bin => exact LevelsBelow.bin
  | builtin hs => exact LevelsBelow.builtin hs
  | tail => exact LevelsBelow.tail
  | cons => exact LevelsBelow.cons
  | tag => exact LevelsBelow.tag
  | nocases => exact LevelsBelow.nocases
  | case_ => exact LevelsBelow.case_
  | select => exact LevelsBelow.select
  | extend => exact LevelsBelow.extend
  | overwrite => exact LevelsBelow.overwrite
  | empty => exact LevelsBelow.empty
  | perform => exact LevelsBelow.perform
  | handle => exact LevelsBelow.handle
  | conv hτ hε _ ih => exact LevelsBelow.conv hτ hε ih

/-- **Existence of a global level cap.** Every derivation has *some* `N` bounding all its reachable
`let_poly`-`defnTy` levels (finite syntax; take the max via `LevelsBelow.mono`). This is the freshness
budget the generalization-level raise spends (offset `o ≥ N`). -/
theorem exists_levelsBelow {m : Type} {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    (h : HasType lvl Γ e τ ε) : ∃ N, LevelsBelow N h := by
  induction h with
  | var hl => exact ⟨0, LevelsBelow.var hl⟩
  | lam hle hfv _ ih =>
      obtain ⟨N, hN⟩ := ih; exact ⟨N, LevelsBelow.lam hle hfv hN⟩
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg ihf iharg =>
      obtain ⟨Nf, hNf⟩ := ihf; obtain ⟨Na, hNa⟩ := iharg
      exact ⟨max Nf Na, LevelsBelow.app (hw := hw)
        (hNf.mono (le_max_left _ _)) (hNa.mono (le_max_right _ _))⟩
  | let_ hdefn hle hfv _ ihd ihb =>
      obtain ⟨Nd, hNd⟩ := ihd; obtain ⟨Nb, hNb⟩ := ihb
      exact ⟨max Nd Nb, LevelsBelow.let_ hle hfv (hNd.mono (le_max_left _ _))
        (hNb.mono (le_max_right _ _))⟩
  | @let_poly lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a hstrict hfv hbodydefn hcw hbody
      ihd ihb =>
      obtain ⟨Nd, hNd⟩ := ihd; obtain ⟨Nb, hNb⟩ := ihb
      refine ⟨max ((Ty.fun argTy εb retTy).levels.foldr max 0 + 1) (max Nd Nb),
        LevelsBelow.let_poly (hcw := hcw) hstrict hfv ?_ (hNd.mono ?_) (hNb.mono ?_)⟩
      · intro l hl
        have hle : l ≤ (Ty.fun argTy εb retTy).levels.foldr max 0 := by
          have key : ∀ (ls : List Nat), l ∈ ls → l ≤ ls.foldr max 0 := by
            intro ls hls
            induction ls with
            | nil => simp at hls
            | cons hd tl ih =>
                simp only [List.foldr]
                rcases List.mem_cons.mp hls with rfl | h
                · exact le_max_left _ _
                · exact le_trans (ih h) (le_max_right _ _)
          exact key _ hl
        omega
      · exact le_trans (le_max_left _ _) (le_max_right _ _)
      · exact le_trans (le_max_right _ _) (le_max_right _ _)
  | int => exact ⟨0, LevelsBelow.int⟩
  | str => exact ⟨0, LevelsBelow.str⟩
  | bin => exact ⟨0, LevelsBelow.bin⟩
  | builtin hs => exact ⟨0, LevelsBelow.builtin hs⟩
  | tail => exact ⟨0, LevelsBelow.tail⟩
  | cons => exact ⟨0, LevelsBelow.cons⟩
  | tag => exact ⟨0, LevelsBelow.tag⟩
  | nocases => exact ⟨0, LevelsBelow.nocases⟩
  | case_ => exact ⟨0, LevelsBelow.case_⟩
  | select => exact ⟨0, LevelsBelow.select⟩
  | extend => exact ⟨0, LevelsBelow.extend⟩
  | overwrite => exact ⟨0, LevelsBelow.overwrite⟩
  | empty => exact ⟨0, LevelsBelow.empty⟩
  | perform => exact ⟨0, LevelsBelow.perform⟩
  | handle => exact ⟨0, LevelsBelow.handle⟩
  | conv _ hτ hε ih =>
      obtain ⟨N, hN⟩ := ih; exact ⟨N, LevelsBelow.conv hτ hε hN⟩

/-! ## Context raise `raiseCtx` (relabel generalization levels `≥ t` by a uniform offset)

The generalization-level raise re-tags every reachable `let_poly`'s gen level `k ↦ k + o` (for `k` at
or above a threshold `t`), which — because a `let_poly`'s stored scheme is `genAtV k defnTy` — forces
the corresponding **context** binding for the let-bound variable from `genAtV k defnTy` to
`genAtV (k+o) (substAt k (·↦ var (k+o)) defnTy)` (the exact input of `instantiateV_genAtV_relabel`).
`raiseScheme`/`raiseCtx` package that context transformation; bindings whose gen level is *below* `t`
(all `mono` bindings, and any outer poly binding generalized below the raise threshold) are left
literally fixed. -/

/-- Relabel a single scheme for the generalization-level raise: a scheme generalized at a level
`≥ t` has its gen level bumped by `o` and its body's level-`(s.level)` variables relabeled to
`s.level + o` (matching `instantiateV_genAtV_relabel`); a scheme below the threshold is fixed. -/
def raiseScheme (t o : Nat) (s : Scheme) : Scheme :=
  if t ≤ s.level then
    Scheme.genAtV (s.level + o) (Ty.substAt s.level (fun i => Ty.var (s.level + o) i) s.body)
  else s

/-- A scheme whose gen level is strictly below the threshold is fixed by the raise. -/
@[simp] theorem raiseScheme_of_level_lt {t o : Nat} {s : Scheme} (h : s.level < t) :
    raiseScheme t o s = s := by
  simp only [raiseScheme, if_neg (Nat.not_le.mpr h)]

/-- Every `mono` binding is fixed by the raise (its gen level is `0 < t`). -/
@[simp] theorem raiseScheme_mono {t o : Nat} (ht : 0 < t) (τ : Ty) :
    raiseScheme t o (Scheme.mono τ) = Scheme.mono τ :=
  raiseScheme_of_level_lt (by simpa [Scheme.mono] using ht)

/-- Apply the generalization-level raise to every scheme in a typing context. -/
def raiseCtx (t o : Nat) (Γ : Ctx) : Ctx :=
  Γ.map (fun b => (b.1, raiseScheme t o b.2))

@[simp] theorem raiseCtx_nil (t o : Nat) : raiseCtx t o [] = [] := rfl

@[simp] theorem raiseCtx_cons (t o : Nat) (x : String) (s : Scheme) (Γ : Ctx) :
    raiseCtx t o ((x, s) :: Γ) = (x, raiseScheme t o s) :: raiseCtx t o Γ := rfl

/-- Context lookup commutes with `raiseCtx` (keys preserved). -/
theorem raiseCtx_lookup {t o : Nat} {Γ : Ctx} {x : String} {s : Scheme}
    (h : Γ.lookup x = some s) : (raiseCtx t o Γ).lookup x = some (raiseScheme t o s) := by
  induction Γ with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
      obtain ⟨y, sy⟩ := hd
      simp only [raiseCtx_cons, List.lookup_cons] at h ⊢
      by_cases hxy : (x == y) = true
      · simp only [hxy] at h ⊢; cases h; rfl
      · simp only [hxy] at h ⊢; exact ih h

/-- **The raise fixes a context all of whose bindings are generalized below the threshold `t`.**
Every `mono` binding (gen level `0`) and every poly binding generalized below `t` is left literally
unchanged, so a context whose bindings all have `s.level < t` is fixed. -/
theorem raiseCtx_fix {t o : Nat} {Γ : Ctx} (hΓ : ∀ b ∈ Γ, b.2.level < t) :
    raiseCtx t o Γ = Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨y, s⟩ := hd
      simp only [raiseCtx_cons, raiseScheme_of_level_lt (hΓ (y, s) (by simp)),
        ih (fun b hb => hΓ b (List.mem_cons_of_mem _ hb))]

/-- **The `var`-arm equality of the generalization-level raise.** For a context binding
`genAtV k d` whose gen level `k` is at or above the raise threshold `t` (so `raiseScheme` relabels
it) and whose body levels are all `< N ≤ o` (freshness budget, from `LevelsBelow` of the enclosing
`let_poly`), there is a **padded** argument list `args'` under which the *relabeled* scheme
instantiates to exactly the original type `(genAtV k d).instantiateV args`. This is the crux
computation the `hasType_raise` var arm performs when it looks up a raised context binding:
`HasType.var` in the raised context produces `(raiseScheme t o (genAtV k d)).instantiateV args'`,
which this lemma shows equals the fixed conclusion type. Composes `instantiateV_pad_default` (extend
`args` to meet the coverage bound without changing the produced type) with
`instantiateV_genAtV_relabel` (the fresh relabel is instantiation-invariant). -/
theorem raiseScheme_genAtV_instantiateV {t o k N : Nat} (hoN : N ≤ o) (hot : 0 < o)
    (htk : t ≤ k) {d : Ty} (hd : ∀ l ∈ d.levels, l < N) (args : List Ty) :
    ∃ args', (raiseScheme t o (Scheme.genAtV k d)).instantiateV args'
      = (Scheme.genAtV k d).instantiateV args := by
  have hlvl : (Scheme.genAtV k d).level = k := rfl
  have hbdy : (Scheme.genAtV k d).body = d := rfl
  have hrs : raiseScheme t o (Scheme.genAtV k d)
      = Scheme.genAtV (k + o) (Ty.substAt k (fun i => Ty.var (k + o) i) d) := by
    simp only [raiseScheme, hlvl, hbdy, if_pos htk]
  have hf : (k + o) ∉ d.levels := fun hmem => absurd (hd _ hmem) (by omega)
  have hne : (k + o) ≠ k := by omega
  set extra := (Ty.freeVarsAt k d).foldr max 0 + 1 with hextra
  refine ⟨args ++ (List.range extra).map (fun j => Ty.var k (args.length + j)), ?_⟩
  have hcov : ∀ i ∈ Ty.freeVarsAt k d,
      i < (args ++ (List.range extra).map (fun j => Ty.var k (args.length + j))).length := by
    intro i hi
    have hle : i ≤ (Ty.freeVarsAt k d).foldr max 0 := by
      have key : ∀ (ls : List Nat), i ∈ ls → i ≤ ls.foldr max 0 := by
        intro ls hls
        induction ls with
        | nil => simp at hls
        | cons hd' tl ih =>
            simp only [List.foldr]
            rcases List.mem_cons.mp hls with rfl | h
            · exact le_max_left _ _
            · exact le_trans (ih h) (le_max_right _ _)
      exact key _ hi
    simp only [List.length_append, List.length_map, List.length_range, hextra]
    omega
  rw [hrs, instantiateV_genAtV_relabel hne hf hcov]
  exact instantiateV_pad_default args extra

/-- **`CtxWfV` is stable (level-shifted) under the generalization-level raise.** A context whose every
binding's body levels are `< lvl` still has every raised binding's body levels `< lvl + o`: bindings
below the threshold `t` are fixed (`< lvl < lvl + o`); a raised binding `genAtV k d ↦
genAtV (k+o) (substAt k (·↦var (k+o)) d)` has body levels either inherited from `d` (`< lvl < lvl+o`)
or the relabel target `k+o` — and `k+o` occurs only if `k ∈ d.levels`, whence `k < lvl` (via the
`CtxWfV` bound on `d`) so `k+o < lvl+o`. The `let_poly`-arm obligation of the generalization-level
raise induction (`raiseCtx` re-tags the internally-introduced `genAtV` bindings; this keeps the
recorded `CtxWfV` side-condition valid at the raised ambient). -/
theorem ctxWfV_raiseCtx {lvl t o : Nat} {Γ : Ctx} (hΓ : CtxWfV lvl Γ) :
    CtxWfV (lvl + o) (raiseCtx t o Γ) := by
  intro b hb l hl
  simp only [raiseCtx, List.mem_map] at hb
  obtain ⟨⟨y, s⟩, hmem, rfl⟩ := hb
  simp only [raiseScheme] at hl
  by_cases hts : t ≤ s.level
  · simp only [if_pos hts, Scheme.genAtV] at hl
    rcases Ty.mem_levels_substAt_strong hl with hl' | ⟨hsl, i, hi⟩
    · exact Nat.lt_of_lt_of_le (hΓ (y, s) hmem l hl') (Nat.le_add_right _ _)
    · simp only [Ty.levels, List.mem_singleton] at hi; subst hi
      exact Nat.add_lt_add_right (hΓ (y, s) hmem s.level hsl) o
  · simp only [if_neg hts] at hl
    exact Nat.lt_of_lt_of_le (hΓ (y, s) hmem l hl) (Nat.le_add_right _ _)

/-! ## The uniform generalization-level raise `hasType_fullRaise`

The sessions G7–G15 sought a *type-fixed* raise (bump every reachable `let_poly`'s gen level `≥ t`,
holding the conclusion type/effect **literally fixed**) so a value-restricted closure whose body
sublevel `lvl' = lvl` could be re-derived with `lvl' > lvl` while keeping its scheme `genAtV lvl defnTy`
unchanged — which the closure-readiness wrapper needs. That raise hits a genuine **two-modes wall**
(G13/G15): its `let_poly` arm must relabel the defn's *own* gen level while keeping *foreign* `≥ t`
levels fixed (reproduced at var uses), but at nesting depth `≥ 2` a defn carries a foreign `≥ t` gen
level, at which the single-level `raiseScheme` and the defn's needed relabel diverge — the two modes
demand incompatible context-raise ops on the shared ambient context.

The **uniform** raise below collapses those two modes into one by giving up "type-fixed": it relabels
**every** `≥ t` level by `o` uniformly — types, effects, context, and every gen level — so its
`let_poly` arm's defn is handled by the *same* theorem (the stored scheme becomes
`genAtV (k+o) (raiseTy t o defnTy)`, exactly the defn's raised type). A single structural induction,
no mutual recursion, no freshness budget, no argument padding. Its limitation (why it does not by
itself discharge the wrapper): it raises the outer scheme's **own** to-be-generalized level-`lvl`
variables too, collapsing `genAtV lvl defnTy` — so it re-derives the *same term* at a *raised* scheme,
not the original one. It is nonetheless the first machine-checked derivation-level generalization-level
raise, and — via `Scheme.instantiateV_genAtV_raiseTy` — relates the raised scheme's instantiations to
the raise of the original's, the bridge a ground-runtime-args closure argument would consume. -/

/-- Uniform scheme raise: shift the gen level `≥ t` by `o`, relabel the body uniformly, keep arity. -/
def raiseScheme_U (t o : Nat) (s : Scheme) : Scheme :=
  ⟨s.arity, if t ≤ s.level then s.level + o else s.level, Ty.raiseTy t o s.body⟩

@[simp] theorem raiseScheme_U_mono {t o : Nat} (ht : 1 ≤ t) (τ : Ty) :
    raiseScheme_U t o (Scheme.mono τ) = Scheme.mono (Ty.raiseTy t o τ) := by
  simp only [raiseScheme_U, Scheme.mono, if_neg (by omega : ¬ t ≤ 0)]

/-- A `genAtV`-canonical binding raises to the relabeled `genAtV` at the shifted level (`t ≤ k`). -/
theorem raiseScheme_U_genAtV {t o k : Nat} (htk : t ≤ k) (d : Ty) :
    raiseScheme_U t o (Scheme.genAtV k d) = Scheme.genAtV (k + o) (Ty.raiseTy t o d) := by
  refine Scheme.ext' ?_ ?_ rfl
  · simp only [raiseScheme_U, Scheme.genAtV]
    exact (Ty.length_filter_levels_raiseTy htk d).symm
  · simp only [raiseScheme_U, Scheme.genAtV, if_pos htk]

/-- **Instantiation of a uniformly-raised scheme** reproduces the raise of the original instantiation,
at the `raiseTy`-relabeled args — for **any** scheme (mono/`genAtV`/arbitrary), no canonicity needed. -/
theorem instantiateV_raiseScheme_U (t o : Nat) (s : Scheme) (args : List Ty) :
    (raiseScheme_U t o s).instantiateV (args.map (Ty.raiseTy t o))
      = Ty.raiseTy t o (s.instantiateV args) := by
  simp only [raiseScheme_U, Scheme.instantiateV]
  by_cases h0 : s.arity = 0
  · simp only [h0, if_true]
  · simp only [h0, if_false]
    rw [Ty.raiseTy_substAt_comm t o s.level _ s.body]
    congr 1
    funext i
    by_cases hi : i < args.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
        Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi, Option.getD_some]
    · have hge : args.length ≤ i := Nat.le_of_not_lt hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_none (by simpa using hge),
        Option.map_none, Option.getD_none, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none hge, Option.getD_none]
      by_cases h : t ≤ s.level <;> simp [Ty.raiseTy, h]

/-- Apply the uniform scheme raise to every binding in a typing context. -/
def raiseCtx_U (t o : Nat) (Γ : Ctx) : Ctx := Γ.map (fun b => (b.1, raiseScheme_U t o b.2))

@[simp] theorem raiseCtx_U_cons (t o : Nat) (x : String) (s : Scheme) (Γ : Ctx) :
    raiseCtx_U t o ((x, s) :: Γ) = (x, raiseScheme_U t o s) :: raiseCtx_U t o Γ := rfl

theorem raiseCtx_U_lookup {t o : Nat} {Γ : Ctx} {x : String} {s : Scheme}
    (h : Γ.lookup x = some s) : (raiseCtx_U t o Γ).lookup x = some (raiseScheme_U t o s) := by
  induction Γ with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
      obtain ⟨y, sy⟩ := hd
      simp only [raiseCtx_U_cons, List.lookup_cons] at h ⊢
      by_cases hxy : (x == y) = true
      · simp only [hxy] at h ⊢; cases h; rfl
      · simp only [hxy] at h ⊢; exact ih h

/-- **`CtxWfV` shifts under the uniform context raise** (every raised body level is the image of an
original `< lvl` level, hence `< lvl + o`). -/
theorem ctxWfV_raiseCtx_U {lvl t o : Nat} {Γ : Ctx} (hΓ : CtxWfV lvl Γ) :
    CtxWfV (lvl + o) (raiseCtx_U t o Γ) := by
  intro b hb l hl
  simp only [raiseCtx_U, List.mem_map] at hb
  obtain ⟨⟨y, s⟩, hmem, rfl⟩ := hb
  simp only [raiseScheme_U] at hl
  rw [Ty.levels_raiseTy, List.mem_map] at hl
  obtain ⟨l', hl'mem, rfl⟩ := hl
  have hlt := hΓ (y, s) hmem l' hl'mem
  split <;> omega

/-- **The uniform generalization-level raise.** Relabels every level `≥ t` by `o` throughout a
derivation — types, effects, context, and every reachable `let_poly`'s gen level — uniformly. A
single structural induction: no mutual recursion, no two-modes conflict, no freshness/coverage
bookkeeping (the `var` arm uses `instantiateV_raiseScheme_U` with `args.map (raiseTy t o)`; the
`let_poly` arm's defn is handled by the same theorem since its raised type `raiseTy t o defnTy`
matches the raised stored scheme `genAtV (k+o) (raiseTy t o defnTy)`). -/
theorem hasType_fullRaise {t o : Nat} (ht : 1 ≤ t)
    {lvl : Nat} {Γ : Ctx} {e : Tree.Node m} {τ ε : Ty}
    (h : HasType lvl Γ e τ ε) (htlvl : t ≤ lvl) :
    HasType (lvl + o) (raiseCtx_U t o Γ) e (Ty.raiseTy t o τ) (Ty.raiseTy t o ε) := by
  revert htlvl
  induction h with
  | @var lvl Γ x s args ε a hl =>
      intro htlvl
      have := HasType.var (m := m) (lvl := lvl + o) (Γ := raiseCtx_U t o Γ) (x := x)
        (s := raiseScheme_U t o s) (args := args.map (Ty.raiseTy t o)) (ε := Ty.raiseTy t o ε)
        (a := a) (raiseCtx_U_lookup hl)
      rwa [instantiateV_raiseScheme_U] at this
  | @builtin lvl Γ id s args ε a hs =>
      intro htlvl
      have hclosed : raiseScheme_U t o s = s := by
        refine Scheme.ext' rfl ?_ ?_
        · simp only [raiseScheme_U, Builtins.scheme_level hs, if_neg (by omega : ¬ t ≤ 0)]
        · simp only [raiseScheme_U]
          exact Ty.raiseTy_eq_self_of_levels_lt
            (fun l hl => by rw [Builtins.scheme_levels_zero hs l hl]; omega)
      rw [← instantiateV_raiseScheme_U t o s args, hclosed]
      exact HasType.builtin (m := m) (lvl := lvl + o) (Γ := raiseCtx_U t o Γ)
        (args := args.map (Ty.raiseTy t o)) (ε := Ty.raiseTy t o ε) (a := a) hs
  | @lam lvl lvl' Γ x body argTy εb retTy ε a hle hfv hbody ih =>
      intro htlvl
      simp only [Ty.raiseTy]
      refine HasType.lam (lvl' := lvl' + o) (by omega) ?_ ?_
      · intro l hl
        rw [Ty.levels_raiseTy, List.mem_map] at hl
        obtain ⟨l', hl'mem, rfl⟩ := hl
        have := hfv l' hl'mem
        split <;> omega
      · have hb := ih (le_trans htlvl hle)
        rw [raiseCtx_U_cons, raiseScheme_U_mono ht] at hb
        exact hb
  | @app lvl Γ f arg argTy εf retTy ε a hf hw harg ihf iharg =>
      intro htlvl
      have hf' := ihf htlvl
      simp only [Ty.raiseTy] at hf'
      exact HasType.app hf' (Ty.raiseTy_effWeaken t o hw) (iharg htlvl)
  | @let_ lvl lvl' Γ x defn body defnTy bodyTy ε a hdefn hle hfv hbody ihdefn ihbody =>
      intro htlvl
      have hb := ihbody (le_trans htlvl hle)
      rw [raiseCtx_U_cons, raiseScheme_U_mono ht] at hb
      refine HasType.let_ (ihdefn htlvl) (by omega) ?_ hb
      intro l hl
      rw [Ty.levels_raiseTy, List.mem_map] at hl
      obtain ⟨l', hl'mem, rfl⟩ := hl
      have := hfv l' hl'mem
      split <;> omega
  | @let_poly lvl lvl' Γ x lx lbody la body argTy εb retTy bodyTy ε a hstrict hfv hbodydefn hcw hbody
      ihdefn ihbody =>
      intro htlvl
      have hbd := ihdefn (by omega : t ≤ lvl')
      rw [raiseCtx_U_cons, raiseScheme_U_mono ht] at hbd
      have hb := ihbody (by omega : t ≤ lvl + 1)
      rw [raiseCtx_U_cons, raiseScheme_U_genAtV htlvl] at hb
      simp only [Ty.raiseTy] at hb
      have hcw' : CtxWfV (lvl + o) (raiseCtx_U t o Γ) := ctxWfV_raiseCtx_U hcw
      refine HasType.let_poly (a := a) (by omega : lvl + o < lvl' + o) ?_ hbd hcw' ?_
      · intro l hl
        rw [Ty.levels_raiseTy, List.mem_map] at hl
        obtain ⟨l', hl'mem, rfl⟩ := hl
        have := hfv l' hl'mem
        split <;> omega
      · rw [show lvl + 1 + o = lvl + o + 1 from by omega] at hb; exact hb
  | int => intro _; simp only [Ty.raiseTy]; exact HasType.int
  | str => intro _; simp only [Ty.raiseTy]; exact HasType.str
  | bin => intro _; simp only [Ty.raiseTy]; exact HasType.bin
  | tail => intro _; simp only [Ty.raiseTy]; exact HasType.tail
  | cons => intro _; simp only [Ty.raiseTy]; exact HasType.cons
  | tag => intro _; simp only [Ty.raiseTy]; exact HasType.tag
  | nocases => intro _; simp only [Ty.raiseTy]; exact HasType.nocases
  | case_ => intro _; simp only [Ty.raiseTy]; exact HasType.case_
  | select => intro _; simp only [Ty.raiseTy]; exact HasType.select
  | extend => intro _; simp only [Ty.raiseTy]; exact HasType.extend
  | overwrite => intro _; simp only [Ty.raiseTy]; exact HasType.overwrite
  | empty => intro _; simp only [Ty.raiseTy]; exact HasType.empty
  | perform => intro _; simp only [Ty.raiseTy]; exact HasType.perform
  | handle => intro _; simp only [Ty.raiseTy]; exact HasType.handle
  | conv _ hτ hε ih =>
      intro htlvl
      exact HasType.conv (ih htlvl) (Ty.raiseTy_tyEquiv t o hτ) (Ty.raiseTy_tyEquiv t o hε)

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

/-! ### G1 Phase 6 regression: sequential `let_poly` (the `PolyAbove` wall, now fixed)

The program `let a = \x.x in (let c = \z.z in c)` — both value-restricted, both generalized — was the
machine-checked counterexample that broke the blanket-`PolyAbove` keystone (Session B): discharging
the inner `c`'s readiness at opening level `2` under `Γ = [(a, genAtV 1 (α→α))]` needs `PolyAbove 2 Γ`,
which is **false** (`a.level = 1 < 2`, `a.arity = 2`). The free-variable-aware `PolyAboveFV` fixes it:
`\z.z` never references `a`, so its free-variable set is empty and the precondition holds vacuously. -/

/-- The outer binding `a : ∀. α → α` at generalization level `1`. -/
private def defnA : Ty := .fun (.var 1 0) .empty (.var 1 0)
/-- The inner binding `c : ∀. β → β` at generalization level `2`. -/
private def defnC : Ty := .fun (.var 2 0) .empty (.var 2 0)
/-- The ambient context inside the inner `let` (only the outer polymorphic `a`). -/
private def Γseq : Ctx := [("a", Scheme.genAtV 1 defnA)]

/-- **The fix, as a lemma.** `\z.z` has no free variables, so it references none of `Γseq`'s
(lower-level) polymorphic bindings — `PolyAboveFV 2 Γseq (\z.z)` holds vacuously. -/
private theorem polyAboveFV_idlam : PolyAboveFV 2 Γseq (lambda "z" (variable_ "z")) := by
  intro y hy
  exact nomatch hy

/-- `Γseq` is below level `2` (`a`'s only level tag is `1 < 2`). -/
private theorem ctxWfV_Γseq : CtxWfV 2 Γseq := by
  intro b hb l hl
  rcases List.mem_singleton.mp hb with rfl
  simp [Scheme.genAtV, defnA, Ty.levels] at hl
  omega

-- **The wall (machine-checked).** Blanket `PolyAbove 2 Γseq` is provably FALSE — the exact obstruction
-- Session B stopped on (`a.arity = 2`, `a.level = 1`, so neither `2 = 0` nor `2 < 1`).
example : ¬ PolyAbove 2 Γseq := by
  intro h
  exact absurd (h ("a", Scheme.genAtV 1 defnA) (by simp [Γseq])) (by decide)

-- **The readiness keystone fires** for `c` at opening level `2` under `Γseq` — where `PolyAbove` is
-- false — producing a genuine instantiation `\z.z : Integer → Integer` (`β ↦ integer`), the
-- preservation obligation the wall blocked.
example : HasType (m := Unit) 2 Γseq (lambda "z" (variable_ "z"))
    ((Scheme.genAtV 2 defnC).instantiateV [.integer]) .empty := by
  have hkey := genAtV_instantiate_lam_ready (m := Unit) (ℓ := 2) (lvl' := 3)
    (x := "z") (lbody := variable_ "z") (la := ()) (argTy := .var 2 0)
    (εb := .empty) (retTy := .var 2 0) (ε := .empty)
    (by decide) (by decide)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    (HasType.var (s := .mono (.var 2 0)) (args := []) rfl)
    polyAboveFV_idlam ctxWfV_Γseq
    [.integer]
    (by intro t ht l hl; simp only [List.mem_singleton] at ht; subst ht;
        exact absurd hl (by simp [Ty.levels]))
  exact hkey

-- The instantiation is genuinely `Integer → Integer` (not vacuous / not identity).
example : (Scheme.genAtV 2 defnC).instantiateV [.integer] = .fun .integer .empty .integer := by
  decide

-- **The whole sequential program type-checks** at `HasType 1 []` (both lets generalized: `a` at
-- level 1, `c` at level 2), the inner `c` instantiated to `Integer → Integer`.
example : HasType (m := Unit) 1 []
    (let_ "a" (lambda "x" (variable_ "x"))
      (let_ "c" (lambda "z" (variable_ "z")) (variable_ "c")))
    ((Scheme.genAtV 2 defnC).instantiateV [.integer]) .empty := by
  refine HasType.let_poly (lvl' := 2) (argTy := .var 1 0) (εb := .empty) (retTy := .var 1 0)
    (by decide)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    (HasType.var (s := .mono (.var 1 0)) (args := []) rfl) ?hcwA ?hbodyA
  case hcwA => intro b hb; exact absurd hb (by simp)
  case hbodyA =>
    refine HasType.let_poly (lvl' := 3) (argTy := .var 2 0) (εb := .empty) (retTy := .var 2 0)
      (by decide)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
      (HasType.var (s := .mono (.var 2 0)) (args := []) rfl) ?hcwC ?hbodyC
    case hcwC => exact ctxWfV_Γseq
    case hbodyC =>
      exact HasType.var (s := Scheme.genAtV 2 defnC) (args := [.integer]) rfl

/-! ### G1 Session C regression: the *referencing* case

`let a = \x.x in (let c = \w. a w in c)` — the inner generalized `c`'s body **references** the outer,
lower-level polymorphic `a` (`a.level = 1 < ℓ = 2`). Session B2's `ℓ < s.level` disjunct of
`PolyAboveFV` was **false** here, so the keystone could not fire. The weakened disjunct
`s.level ≠ 0 ∧ s.level ≠ ℓ` admits `a` (`1 ≠ 0 ∧ 1 ≠ 2`), and the tightened args side-condition
(`l = 0 ∨ l = s.level`) recovers the `var`-arm cleanliness w.r.t. `a`'s level `1` — so re-typing
`c`'s body under `substAt 2` leaves the referenced `a`'s own instantiation fixed. -/

/-- `c`'s body `a w` (`a` referenced, `w` the parameter). -/
private def cRefBody : Tree.Node Unit := apply (variable_ "a") (variable_ "w")
/-- The context inside `c`'s lambda: the parameter `w` (mono) over the outer polymorphic `a`. -/
private def Γc : Ctx := [("w", Scheme.mono (.var 2 0)), ("a", Scheme.genAtV 1 defnA)]

/-- **The referencing case is admitted.** `\w. a w` references `a` (level `1`), but the weakened
`PolyAboveFV` holds (`a.level = 1 ≠ 0` and `≠ 2`) — where the old `2 < 1` disjunct was false. -/
private theorem freeVars_reflam : (lambda "w" cRefBody).freeVars = ["a"] := by decide

private theorem polyAboveFV_reflam :
    PolyAboveFV 2 Γseq (lambda "w" cRefBody) := by
  intro y hy s hlk
  rw [freeVars_reflam, List.mem_singleton] at hy
  subst hy
  simp only [Γseq, List.lookup_cons, beq_self_eq_true, if_true] at hlk
  cases hlk
  exact Or.inr ⟨by decide, by decide⟩

/-- `c`'s body types (level `3`): `a` instantiated at `[var 2 0]` gives `(var 2 0) → (var 2 0)`,
applied to `w : var 2 0`. This is the derivation whose `substAt 2` re-typing the keystone runs. -/
private theorem hbody_ref : HasType (m := Unit) 3 Γc cRefBody (.var 2 0) .empty := by
  have haType : (Scheme.genAtV 1 defnA).instantiateV [.var 2 0]
      = .fun (.var 2 0) .empty (.var 2 0) := by decide
  have ha : HasType (m := Unit) 3 Γc (variable_ "a") (.fun (.var 2 0) .empty (.var 2 0)) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3) (Γ := Γc) (x := "a")
      (s := Scheme.genAtV 1 defnA) (args := [.var 2 0]) (ε := .empty) (a := ()) (by decide)
    rwa [haType] at h
  have hw : HasType (m := Unit) 3 Γc (variable_ "w") (.var 2 0) .empty := by
    have h := HasType.var (m := Unit) (lvl := 3) (Γ := Γc) (x := "w")
      (s := Scheme.mono (.var 2 0)) (args := ([] : List Ty)) (ε := .empty) (a := ()) (by decide)
    rwa [Scheme.instantiateV_mono] at h
  exact HasType.app ha (Ty.effWeaken_refl _) hw

-- **The readiness keystone fires** for the referencing `c` at opening level `2` under `Γseq`,
-- instantiating `c` to `Integer → Integer` — the exact obligation the referencing gap blocked.
example : HasType (m := Unit) 2 Γseq (lambda "w" cRefBody)
    ((Scheme.genAtV 2 defnC).instantiateV [.integer]) .empty := by
  have hkey := genAtV_instantiate_lam_ready (m := Unit) (ℓ := 2) (lvl' := 3)
    (x := "w") (lbody := cRefBody) (la := ()) (argTy := .var 2 0)
    (εb := .empty) (retTy := .var 2 0) (ε := .empty)
    (by decide) (by decide)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbody_ref
    polyAboveFV_reflam ctxWfV_Γseq
    [.integer]
    (by intro t ht l hl; simp only [List.mem_singleton] at ht; subst ht;
        exact absurd hl (by simp [Ty.levels]))
  exact hkey

-- **The whole referencing program type-checks** at `HasType 1 []`, `c` instantiated to
-- `Integer → Integer`, with `c`'s body genuinely referencing the outer polymorphic `a`.
example : HasType (m := Unit) 1 []
    (let_ "a" (lambda "x" (variable_ "x"))
      (let_ "c" (lambda "w" cRefBody) (variable_ "c")))
    ((Scheme.genAtV 2 defnC).instantiateV [.integer]) .empty := by
  refine HasType.let_poly (lvl' := 2) (argTy := .var 1 0) (εb := .empty) (retTy := .var 1 0)
    (by decide)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    (HasType.var (s := .mono (.var 1 0)) (args := []) rfl) ?hcwA ?hbodyA
  case hcwA => intro b hb; exact absurd hb (by simp)
  case hbodyA =>
    refine HasType.let_poly (lvl' := 3) (argTy := .var 2 0) (εb := .empty) (retTy := .var 2 0)
      (by decide)
      (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
      hbody_ref ?hcwC ?hbodyC
    case hcwC => exact ctxWfV_Γseq
    case hbodyC =>
      exact HasType.var (s := Scheme.genAtV 2 defnC) (args := [.integer]) rfl

-- **The design correction, non-vacuously validated.** The lambda `\w. a w` — whose body `hbody_ref`
-- carries the **non-ground** instantiation arg `[.var 2 0]` (level 2 ≠ `a.level` = 1) — is `HasTypeRT`
-- **regardless** of that body: `HasTypeRT.lam` takes no premise on `hbody`. This is exactly why the
-- `lam` arm must not recurse: a legitimately-typed lambda with a non-ground body var arg is still a
-- valid runtime control (it becomes a closure; its body is re-typed with ground args only when
-- applied). Had `lam` recursed into `hbody`, this — and hence the whole referencing program above —
-- would fail to be `HasTypeRT`.
example : HasTypeRT
    (@HasType.lam Unit 2 3 Γseq "w" cRefBody (.var 2 0) .empty (.var 2 0) .empty ()
      (by decide) (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
      hbody_ref) :=
  @HasTypeRT.lam Unit 2 3 Γseq "w" cRefBody (.var 2 0) .empty (.var 2 0) .empty ()
    (by decide) (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    hbody_ref

/-! ### G1 Session F witness: the `genAtV_closure_ready_value` strictness gap is NOT the
runtime-groundness obstruction

Session E conjectured that the wrapper's residual `ℓ < lvl'` strictness gap and the var-preservation
"runtime groundness" blocker were **the same obstruction**, both closable together by `HasTypeRT`.
This machine-checked witness **refutes** that: the strictness gap has a reachable, **fully ground**
instance that no groundness invariant excludes.

Take the value-restricted closure `\x. perform "op" x`. Typed at ambient level `1`, its body sublevel
is `lvl' = 1` (the arg type is ground, so `∀ l ∈ argTy.levels, l < 1` holds vacuously — `lam` does not
force `lvl'` up). Its type `defnPerf = integer →⟨op:(integer,integer)|μ⟩ integer` carries a **generalizable
effect tail** `μ = var 1 0` at level `1`. So a `let`-generalizing it at `ℓ = lvl = 1` produces
`genAtV 1 defnPerf` with `arity ≠ 0` (the `μ` occurrence) while `lvl' = ℓ = 1` — the wrapper's arity≠0
branch fires with the **non-strict** `ℓ = lvl'`, and `genAtV_closure_ready_value`'s `hlt : ℓ < lvl'`
(needed by `hasType_subst`'s `let_poly` arm to keep the opening level off any inner generalization) is
unavailable.

Crucially the derivation is **ground**: the only `.Variable` node instantiates `.mono integer` at
`args = []`, and the level-`1` tag comes from the `perform` rule's freely-chosen effect tail `μ`, **not**
from any instantiation argument. So `HasTypeRT` (which only bounds `var`/`builtin` args) leaves this case
open. The real fix is orthogonal: `hasType_subst` needs to admit `ℓ ≤ lvl'` whenever **no `let_poly` in
the body generalizes at exactly `ℓ`** (here the body has no `let_poly` at all), a derivation-level side
condition — not a groundness bound. See the Session F progress note. -/
private def defnPerf : Ty :=
  .fun .integer (.effectExtend "op" .integer .integer (.var 1 0)) .integer

-- `\x. perform "op" x` types at ambient level `1` with body sublevel `lvl' = 1` (non-strict).
example : HasType (m := Unit) 1 []
    (lambda "x" (apply (perform "op") (variable_ "x"))) defnPerf .empty := by
  refine HasType.lam (lvl' := 1) (le_refl _) ?_ ?_
  · intro l hl; simp only [Ty.levels] at hl; exact absurd hl (by simp)
  · refine HasType.app (argTy := .integer)
      (εf := .effectExtend "op" .integer .integer (.var 1 0)) HasType.perform
      (Ty.effWeaken_refl _) ?_
    exact HasType.var (s := .mono .integer) (args := []) rfl

-- Its scheme generalized at level `1` has `arity ≠ 0` (the effect tail `μ = var 1 0`) — so the wrapper
-- reaches its arity≠0 branch with `lvl' = ℓ = 1`, where the strict `ℓ < lvl'` is unavailable.
example : (Scheme.genAtV 1 defnPerf).arity ≠ 0 := by decide

/-! ### G1 Session G6: `NoGenAt` is a *judgment*-level property (proof irrelevance); route (a) holds
for the residual-corner witness via level-normalization

Session G5 decomposed the closure-readiness wrapper's residual `NoGenAt lvl hbody` need to exactly the
corner `arity ≠ 0 ∧ lvl' = lvl`, and asked (route (a)) whether that `NoGenAt` is derivable. Two findings
this session, one structural, one machine-checked on the hardest known witness.

**(1) `NoGenAt` is proof-irrelevant — it is a property of the *judgment*, not the specific derivation.**
`NoGenAt ℓ` is a `Prop` indexed by a `HasType` *proof*, and `HasType` is itself a `Prop`; Lean's
definitional proof irrelevance makes any two proofs of the same judgment defeq, so `NoGenAt ℓ h₁` and
`NoGenAt ℓ h₂` are the *same type* whenever `h₁`, `h₂` type the same judgment. Consequently `NoGenAt ℓ h`
means exactly "the judgment `h` proves admits *some* derivation none of whose reachable `let_poly` nodes
generalize at `ℓ`". This **corrects the G5 note's framing** (which treated `NoGenAt` as derivation-
specific and concluded the corner needs an external witness): one only has to exhibit *a* good
derivation of the *same judgment*, e.g. one typing the body at a higher sublevel. A blocking
`cases`/inversion on `NoGenAt` is impossible for the same reason (the proof-term index is irrelevant), so
`¬ NoGenAt` of a self-level `let_poly` derivation is *not* provable and is in fact *false* whenever the
judgment admits any generalization-free (or higher-level) re-derivation.

**(2) The hardest known residual-corner witness satisfies `NoGenAt` via normalization** (machine-checked
below). Take `\x. (let h = \y.y in perform "op" x)`: it types at `defnPerf` (ambient level `1`, stored
`lvl' = 1` — arg type ground so `lam` does not force `lvl'` up), so `genAtV 1 defnPerf` has `arity ≠ 0`
(the effect tail `μ = var 1 0`) — the residual corner — AND its body carries an inner `let_poly`. The
SAME lambda ALSO types at `defnPerf` with `lvl' = 2` (`advPerf_lvl2`), putting the inner `let_poly` at
level `2 > 1`, whence `NoGenAt 1` of the whole lambda holds via `noGenAt_of_lt` (`advPerf_lvl2_noGenAt`).
By proof irrelevance the two derivations are defeq, so this *also* proves `NoGenAt 1 advPerf_lvl1`
(`advPerf_lvl1_noGenAt`) — the wrapper's premise for the un-normalized `lvl' = 1` derivation the runtime
hands us. Route (a) *holds here*; the supposed adversarial witness is not adversarial.

**Scope of what is settled vs. open.** The witness's inner `let_poly` (`h : int → int`, ground) is
*vacuous* — `genAtV n (int→int)` is `arity 0` for every `n`, so bumping `lvl'` is a free "renaming".
The genuinely general theorem needs level **renaming** (not mere weakening: `HasType n Γ e τ ε →
HasType (n+1) Γ e τ ε` is FALSE when an inner `let_poly` generalizes real level-`n` vars, since
`genAtV n d ≠ genAtV (n+1) d`). The true open frontier is a *non-vacuous* inner `let_poly` generalizing
at exactly the collision level `lvl` inside a residual-corner lambda; the right closure is to fold the
renaming normalization *into* `genAtV_closure_ready_value_node`, dropping its `NoGenAt lvl h` premise so
the Soundness site never supplies it. See the Session G6 progress note. -/

-- **G1 Phase 6 (strict-sublevel reshape).** The residual-corner witnesses (`advPerfBody`/`advDefnH`/
-- `advH_defn`/`advPerf_body1`/`advPerf_lvl1`/`advPerf_body2`/`advPerf_lvl2` and their `NoGenAt` lemmas,
-- sessions F/G6) exercised an inner `let_poly` whose defn lambda descends **non-strictly** (`lvl' =
-- lvl`) — the exact "residual corner" the closure-readiness wrapper could not discharge. The `let_poly`
-- constructor now demands a **strict** defn sublevel (`lvl < lvl'`, the Rémy/OCaml fresh-level
-- discipline), so those witnesses are unconstructable **by design**: the corner no longer exists, and
-- `NoGenAt lvl` of the defn holds for free via `noGenAt_of_lt` (see `noGenAt_letpoly_defn`). The
-- witnesses were removed with the reshape (they were private, unreferenced exploration scaffolding). The
-- surviving `escBodyAt`/`escLam_*` witnesses (below) use the already-strict `escH_defn` and are retained.

/-- `Γ = [(x, .mono integer)]` is below any `n ≥ 1`. -/
private theorem advH_ctxwf {n : Nat} (hn : 1 ≤ n) :
    CtxWfV n [("x", Scheme.mono .integer)] := by
  intro b hb l hl
  rcases List.mem_singleton.mp hb with rfl
  simp only [Scheme.mono, Ty.levels, List.not_mem_nil] at hl

/-! ### G1 Session G8: the *escaping* inner `let_poly` is freshenable via re-instantiation

Session G7 (Finding 2) exhibited `\x. (let h = \z.z in h)` as an "escape" witness where the inner
`let_poly`'s generalized variable **re-surfaces in the outer lambda's result type** (`retTy = β → β`
with `β` at exactly the inner generalization level), and conjectured (Finding 4) that such a case must
be handled by **mono-izing** (rebinding `h` monomorphically) rather than **freshening** (bumping the
inner `let_poly` to a higher level), because a naive tag-uniform level shift is ill-defined when the
outer and inner generalized variables share the level tag.

**That dichotomy is imprecise.** The escaping case is *also* freshenable — the mono-ize branch is not
needed. The escaped occurrence in `retTy` is produced by **instantiating** the inner scheme at a
lower-level (outer / ground) variable; that instantiation argument is chosen independently of the
inner scheme's own generalization level, so the inner level can be moved *fresh* while the very same
argument reproduces the identical `retTy`. Concretely: the body `h` is typed by instantiating `h`'s
scheme at `[var 1 0, var 1 0]` — a level-`1` (outer) variable. In the un-normalized derivation the
inner `let_poly` generalizes at level `1`, so that argument collides with the gen level; in the
normalized derivation it generalizes at level `2`, and the identical argument `var 1 0` (level `1 ≠ 2`)
yields the identical `retTy = var 1 0 → var 1 0`. Both derivations prove the **same judgment**; the
normalized one gives `NoGenAt 1` for free via `noGenAt_of_lt`. This is the sharper, more uniform
statement: at a lambda-body site the inner `let_poly` level is a *free choice* (bounded below by the
enclosing binder's sublevel), and re-instantiation keeps `retTy` fixed regardless of whether the
escaped variable is inner-generalized or outer-ambient — there is no representation wall here, and no
principal-types mono-ize obligation. (Compare `advPerf` above, whose inner `let_poly` is *vacuous*
(`h : int→int`, `arity 0`); this witness has a genuinely `arity ≠ 0` inner scheme whose gen variable
truly escapes into `retTy`, the case G7 flagged as the hard one.) -/

/-- The escape body `let h = \z.z in h` — the returned `h` is a polymorphic identity whose scheme's
generalized variable re-surfaces in the result type (via instantiation at the outer `var 1 0`). -/
private def escBody : Tree.Node Unit :=
  let_ "h" (lambda "z" (variable_ "z")) (variable_ "h")

/-- The escape lambda `\x. (let h = \z.z in h)`. -/
private def escLam : Tree.Node Unit := lambda "x" escBody

/-- The **fixed** result type `var 1 0 → var 1 0` (the escaped variable sits at level `1`). -/
private def escRetTy : Ty := .fun (.var 1 0) .empty (.var 1 0)

/-- The **fixed** lambda type `integer → (var 1 0 → var 1 0)`. `genAtV 1 escDefnTy` has `arity 2`
(two level-`1` occurrences in `escRetTy`), so this is the residual `arity ≠ 0` corner. -/
private def escDefnTy : Ty := .fun .integer .empty escRetTy

/-- The residual corner is genuine: the outer scheme quantifies real (level-`1`) variables. -/
example : (Scheme.genAtV 1 escDefnTy).arity = 2 := by decide

/-- The inner `\z.z` typed at gen level `n`: `var n 0 → var n 0`. -/
private theorem escH_defn (n : Nat) :
    HasType (m := Unit) n [("x", Scheme.mono .integer)] (lambda "z" (variable_ "z"))
      (.fun (.var n 0) .empty (.var n 0)) .empty :=
  HasType.lam (lvl' := n + 1) (a := ()) (ε := .empty) (Nat.le_succ _)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    (HasType.var (s := .mono (.var n 0)) (args := []) rfl)

/-- The let body `h`, instantiated at `[var 1 0, var 1 0]`, has type `escRetTy` **independently of the
inner gen level `n`**: re-instantiation reproduces the escaped variable at the fixed level `1`. -/
private theorem escH_body (n : Nat) :
    HasType (m := Unit) (n + 1)
      [("h", Scheme.genAtV n (.fun (.var n 0) .empty (.var n 0))), ("x", Scheme.mono .integer)]
      (variable_ "h") escRetTy .empty := by
  have hinst : (Scheme.genAtV n (.fun (.var n 0) .empty (.var n 0))).instantiateV [.var 1 0, .var 1 0]
      = escRetTy := by
    simp only [escRetTy, Scheme.genAtV, Scheme.instantiateV, Ty.levels]
    cases n <;> simp_all [Ty.substAt, List.getD]
  have h := HasType.var (m := Unit) (lvl := n + 1)
    (Γ := [("h", Scheme.genAtV n (.fun (.var n 0) .empty (.var n 0))), ("x", Scheme.mono .integer)])
    (x := "h") (s := Scheme.genAtV n (.fun (.var n 0) .empty (.var n 0)))
    (args := [.var 1 0, .var 1 0]) (ε := .empty) (a := ()) rfl
  rwa [hinst] at h

/-- The escape body at gen level `n` (`≥ 1`): inner `let_poly` at `n`, result type the fixed
`escRetTy`. -/
private def escBodyAt (n : Nat) (hn : 1 ≤ n) :
    HasType (m := Unit) n [("x", Scheme.mono .integer)] escBody escRetTy .empty :=
  HasType.let_poly (a := ()) (lvl' := n + 1) (argTy := .var n 0) (εb := .empty) (retTy := .var n 0)
    (Nat.lt_succ_self n)
    (by intro l hl; simp only [Ty.levels, List.mem_singleton] at hl; omega)
    (HasType.var (s := .mono (.var n 0)) (args := []) rfl)
    (advH_ctxwf hn) (escH_body n)

/-- **The un-normalized (`lvl' = 1`) escape derivation.** The inner `let_poly` generalizes at exactly
`lvl = 1`; its generalized variable escapes into `retTy = escRetTy`. The residual corner (`arity ≠ 0`,
`lvl' = lvl`) *with a genuine escape* — the case G7 conjectured needs mono-izing. -/
private def escLam_lvl1 : HasType (m := Unit) 1 [] escLam escDefnTy .empty :=
  HasType.lam (lvl' := 1) (a := ()) (ε := .empty) (le_refl _)
    (by intro l hl; simp only [Ty.levels] at hl; exact absurd hl (by simp))
    (escBodyAt 1 (le_refl _))

/-- **The freshened (`lvl' = 2`) escape derivation** — the SAME term, SAME type `escDefnTy`, SAME
ambient level `1`; only the inner `let_poly` moves to level `2`, its use re-instantiated at the
identical `[var 1 0, var 1 0]` so `retTy` is unchanged. -/
private def escLam_lvl2 : HasType (m := Unit) 1 [] escLam escDefnTy .empty :=
  HasType.lam (lvl' := 2) (a := ()) (ε := .empty) (by decide)
    (by intro l hl; simp only [Ty.levels] at hl; exact absurd hl (by simp))
    (escBodyAt 2 (by decide))

/-- The freshened body (inner `let_poly` at `2 > 1`) satisfies `NoGenAt 1` *for free* via
`noGenAt_of_lt` — **no** mono-ize step, **no** principal-types argument, just re-instantiation. -/
private theorem escLam_lvl2_noGenAt : NoGenAt 1 escLam_lvl2 :=
  NoGenAt.lam (by decide)
    (by intro l hl; simp only [Ty.levels] at hl; exact absurd hl (by simp))
    (noGenAt_of_lt (escBodyAt 2 (by decide)) (by decide))

/-- **The escaping witness is freshenable.** `escLam_lvl1` and `escLam_lvl2` prove the identical
judgment, so by proof irrelevance the wrapper's premise `NoGenAt 1 escLam_lvl1` — for the escaping,
un-normalized derivation the runtime hands us — is discharged by the freshened derivation's
`NoGenAt`. **This refutes G7's "escape ⇒ mono-ize" dichotomy**: escape into the result type does not
force mono-ization; re-instantiation at the outer variable keeps `retTy` fixed while the inner level
is freshened. -/
private theorem escLam_lvl1_noGenAt : NoGenAt 1 escLam_lvl1 :=
  escLam_lvl2_noGenAt

end Examples

end Eyg.Types
