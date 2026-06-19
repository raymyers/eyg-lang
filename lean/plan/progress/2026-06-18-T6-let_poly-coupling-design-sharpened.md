---
date: 2026-06-18
milestone: T6 — `let_poly` machine-coupling design, SHARPENED
status: DESIGN SPEC v2 (supersedes the open questions in 2026-06-18-T6-let_poly-coupling-design.md)
---

# `let_poly` — sharpened machine-coupling design

Builds on `2026-06-18-T6-gen-declarative-keystone.md` (keystone `generalizes_closure_ready`,
green) and `2026-06-18-T6-let_poly-coupling-design.md` (Design A vs B). That earlier note left
two things to "pick at implementation time" — *where* readiness is established and *how* the
value becomes visible to the frame typing. This note **resolves both** after tracing the actual
reduction, and corrects a subtlety the earlier note did not surface.

## The corrected subtlety: `env ≠ fenv`, so readiness cannot be reconstructed at the pop

Reduction facts (verified against `Eyg/Semantics/Reduction.lean`):

- **Let push** (`Reduction.lean:241`):
  `E (Let x defn body), env, k  →  E defn, env, (Assign x body env)::k`.
  The Assign frame is pushed carrying **the current `env`** as its `fenv`. So *at the push*
  `fenv = env` holds **definitionally**.
- **Assign pop** (`Reduction.lean:222`):
  `V val, env', (Assign x body fenv)::rest  →  E body, (x,val)::fenv, rest`.
  The bound value extends **`fenv`** (the frame's env), **not** the control env `env'`.

But `preservation_E`/`preservation_V` are stated for a *generic* state matching the pattern, and
`MStateWf` re-inverts existentially each step. So inside the proofs:

- the control's context `Γc` (from `EnvWf env Γc`) and the frame's context `Γf` (from the
  Assign-frame inversion `EnvWf fenv Γf`) are **independent existentials** (`EnvWf` is not
  injective), and `env` vs `fenv` are **independent state fields**.

Consequence (the wall): at the **pop**, the incoming value `val : defnTy` is arbitrary. To
discharge `EnvWf.cons`'s polymorphic clause `∀ args, HasTypeV val (s.instantiate args)` we would
re-run the keystone, which needs one *coherent* `(Γ, EnvWf · Γ, lambda-typing@Γ, Generalizes s Γ
defnTy)`. The frame supplies `Generalizes s Γf defnTy` for `Γf`/`fenv`; the value's only handle
is `HasTypeV val defnTy` (a closure over `env`). `hasTypeV_subst_closure` would need `σ` to fix
**every** `Γc'` the closure's env realizes, but `Generalizes` only fixes the one `Γf`. **So
readiness is NOT reconstructible at the pop.** (This is the "deepened finding" the PLAN's T6 gen
bullet named, now pinned to the exact `env ≠ fenv` / `Γc ≠ Γf` mechanism.)

## The fix: compute readiness at the PUSH (the one coherent point), carry it as a CLOSED fact

At the **Let push** everything is coherent in one context: we have `henv : EnvWf env Γ`,
`hdefn : HasType Γ defn defnTy ε` with `defn = ⟨.Lambda x' body', a'⟩` (value restriction), and
`Generalizes s Γ defnTy` (from `inv_let_poly`). The keystone applies **directly**:

```
Rdy : ∀ args, HasTypeV (Value.Closure x' body' env) (s.instantiate args)
    := generalizes_closure_ready hgen henv hdefn      -- hdefn IS the lambda typing
```

This is a **closed** fact about the *specific* future closure `w := Closure x' body' env`
(`= Closure x' body' fenv`, since `fenv = env` at the push) — no contexts left dangling. The
task is then purely to **carry `Rdy` + the value-coupling `val = w`** from the push, through the
single lambda→closure step, to the pop. (`defn` is syntactically a `λ`, so exactly one step
intervenes; no intermediate states.)

Why the carry is unavoidable (not bolt-on at the value state): the lambda→closure step
(`preservation_E` `Lambda` case) is the transition that would otherwise have to *produce* `Rdy`,
and it hits the same `env ≠ fenv` / `Γc ≠ Γf` wall. So the E-state already standing on the
Assign frame must carry `Rdy` forward; the V-state must carry `val = w` + `Rdy`.

## Concrete design — a value-aware stack predicate `StackWfV`

`MStateWf` is a function of the *runtime* `MState`; the mono/poly flavor of an `Assign` frame is
**not** observable from the runtime stack (`Kontinue.Assign x body fenv` is identical in both
cases — see the earlier note's "irreducible obstacle"). The poly scheme `s` and `Rdy` live in
the *typing*. Trying to bolt a side-predicate `ReadyAt v k` onto `MStateWf` fails: it would have
to existentially re-link its `s` to the `StackWf` proof's `s`, which a function of the runtime
stack cannot do. **So the readiness must be bundled with the stack typing** — a value-aware
inductive `StackWfV`.

### `StackWfV` shape (value-aware only at the head; recurse only through `trace`)

```
inductive StackWfV {m} (v : Value m) : Stack m → Ty → Ty → Ty → Prop
  | nil      : ... (= StackWf.nil)
  | trace    : StackWfV v rest σ ε τ → StackWfV v ((Trace w,a)::rest) σ ε τ   -- v passes through
  | arg / applyf / callwith / delimit :
        -- the head CONSUMES v, so rest does not constrain v: store plain `StackWf rest …`
        … StackWf rest … → StackWfV v ((…,a)::rest) …
  | assign   :  -- MONO: incoming v bound at .mono defnTy; readiness is the trivial single instance
        EnvWf fenv Γ → HasType ((x,.mono defnTy)::Γ) body bodyTy ε → StackWf rest bodyTy ε τ →
        StackWfV v ((Assign x body fenv,a)::rest) defnTy ε τ
  | assignPoly : -- POLY: carry the closed readiness about THIS v
        (∀ args, HasTypeV v (s.instantiate args)) →            -- Rdy (v is the bound subject)
        EnvWf fenv Γ → HasType ((x,s)::Γ) body bodyTy ε → StackWf rest bodyTy ε τ →
        StackWfV v ((Assign x body fenv,a)::rest) defnTy ε τ   -- input endpoint = defnTy
  | conv     : StackWfV v k σ ε τ → TyEquiv σ σ' → TyEquiv ε ε' → StackWfV v k σ' ε' τ
```

Notes:
- Only `assign`/`assignPoly` mention `v`; everything else either passes `v` through (`trace`) or
  drops to plain `StackWf` (the head consumes `v`). So `StackWfV` is ~the size of `StackWf` but
  most arms are trivial wrappers. A forgetful `stackWfV_toStackWf : StackWfV v k σ ε τ → StackWf
  k σ ε τ` (erase `Rdy`, fold `assignPoly`→ a *generalized* `StackWf.assign` storing `s`) is
  immediate by induction.
- `StackWf.assign` must be **generalized to store an arbitrary scheme `s`** (mono = `.mono
  defnTy`) so the forgetful map has a target. This is the only `StackWf` change; its inversion
  `stackWf_assign_inv` returns `s` (mono callers pass `.mono`).

### `MStateWf` becomes value-aware in the value case only

```
| .run (.E e, env, k), τ, ε => ∃ Γ τin, EnvWf env Γ ∧ HasType Γ e τin ε ∧ StackWfE … k τin ε τ
| .run (.V v, _, k), τ, ε   => ∃ τin, HasTypeV v τin ∧ StackWfV v k τin ε τ
| .wait …                   => (unchanged)
```

The E-state also needs to carry `Rdy` forward (it stands on the Assign frame *before* the value
exists). Cleanest: give the E-control case a **future-value-aware** variant `StackWfE`, where the
`assignPoly` head stores `Rdy` about the closure the control *will* become, together with the
coupling `control = ⟨.Lambda x' body',_⟩ ∧ env = fenv ∧ w = Closure x' body' fenv`. The
lambda→closure step then rewrites `control`/`env` and discharges the coupling, handing `Rdy`
(now about the realized `val = w`) to `StackWfV`.

> Implementation choice to make first thing: whether `StackWfE` is a second inductive or whether
> the E-case can store the bare `Generalizes s Γ defnTy` + the let-site `HasType Γ defn defnTy ε`
> (re-running the keystone at the lambda-step is then **sound** because the E-case fixes `Γ = the
> control's `Γc` and `env`** — there is no `env ≠ fenv` split *before* the frame's `fenv` is
> re-existentialized, since the E-case's `EnvWf env Γ` and the stored `Generalizes s Γ` share the
> *same* `Γ`). This may let the E-side avoid storing a precomputed `Rdy` and avoid the `env=fenv`
> equality, pushing all the readiness work to the single lambda-step. **Evaluate both at
> implementation start; the V-side `StackWfV` with closed `Rdy` is fixed either way.**

## Implementation checklist (revised, `MStateWf` world first)

1. **Typing.** Add `HasType.let_poly` (value-restricted: `defn = ⟨.Lambda _ _, _⟩`) with premises
   `HasType Γ defn defnTy ε`, `Generalizes s Γ defnTy`, `HasType ((x,s)::Γ) body bodyTy ε`. Keep
   `HasType.let_` (mono, arbitrary defn). Cascade:
   - `inv_let` → return mono-or-poly (or add `inv_let_poly`); add the `let_poly` arm to
     `hasType_expr_form` (same `.Let` disjunct).
   - new `| let_poly` arms in the **no-catch-all** inductions: `hasType_ctxConv`
     (Typing.lean), `hasType_subst` (Substitution.lean), `weakenEff` (Soundness.lean:57).
     (Other-node inversions have `| _ => simp at he` and absorb it for free.)
2. **Stack typing.** Generalize `StackWf.assign` to store scheme `s`; update `stackWf_assign_inv`
   + `stackSeg_toStackWf`'s assign arm. Add `StackWfV` (+ `stackWfV_toStackWf`, `stackWfV_*_inv`,
   `stackWfV_conv`). Decide E-side (`StackWfE` vs bare-`Generalizes`, see box).
3. **`MStateWf`** value case → `StackWfV v k`. Re-prove `mStateWf_V` accessor.
4. **Preservation/progress (non-B).** `preservation_E` Let-push: build the poly Assign frame
   storing the let-site facts; `Lambda` case: discharge the coupling, hand `Rdy` to `StackWfV`;
   `preservation_V` Assign-pop: read `Rdy`, feed `EnvWf.cons`. Re-green `progress`,
   `soundness_value`. Every existing value-state construction site (`⟨τin, hv, hst⟩`) must now
   produce a `StackWfV` — for non-Assign heads this is the trivial wrapper, so it's mechanical
   but **touches every `.V`-producing arm of `preservation_E`/`preservation_V`**.
5. **Example.** `let id = \x.x in pair (id 1) (id "a")` types polymorphically.
6. **B-world (separate follow-up, REQUIRED for green once the constructor exists).** Adding
   `HasType.let_poly` breaks `preservation_E_B`/`preservation_V_B`/`progress` B-arms and
   `hasType_expr_form` consumers in the base-row engine — they must handle the new constructor
   (mirror steps 2–4 with `StackWfVB`). `let_poly` is **effect-orthogonal** (the bound value is a
   pure closure), so the B-coupling is the same shape; but the build will not compile with a
   half-done B-world. Budget for it in the same slice.

## Import-ordering wrinkle (resolved) — do this first

`HasType.let_poly` needs `Generalizes s Γ defnTy` as a constructor premise, but `Generalizes`
currently lives in `Generalization.lean` (imports `Substitution` → `Typing`), so `HasType` (in
`Typing.lean`) cannot reference it as written — a cycle. **Resolution (verified):** `Generalizes`
and its helper `substCtx` depend only on `Ctx` (`Typing.lean:40`), `Scheme.instantiate`/
`substScheme`, and `Ty.subst` — *all* already available in `Typing.lean` (it imports
`Eyg.Types.Scheme`). So **move the `substCtx` + `Generalizes` `def`s into `Typing.lean`** (just
after the `Ctx` abbrev, before `HasType`); leave their *lemmas* (`substCtx_lookup`,
`substScheme_id`, `generalizes_mono`, `generalizes_closure_ready`, …) where they are in
`Substitution.lean`/`Generalization.lean`. One `def` relocation, no lemma changes; everything
downstream still resolves `substCtx`/`Generalizes` by the same name.

## ⚠ NEW obstacle surfaced by an implementation probe — `Generalizes` × `hasType_ctxConv`

Began the cascade (moved `substCtx`/`Generalizes` into `Typing.lean`, added the `let_poly`
constructor) and hit a real obstacle in the *first* dependent lemma, `hasType_ctxConv`
(`Typing.lean`). That lemma rewrites one context binding's type `.mono σ → .mono σ'` for
`TyEquiv σ' σ` and re-runs every `HasType` rule. The `let_poly` arm needs

```
Generalizes s (Δ ++ (x,.mono σ )::Γ) defnTy   ⟹   Generalizes s (Δ ++ (x,.mono σ')::Γ) defnTy
```

but `Generalizes` fixes the context **syntactically** (`substCtx σg Γ₁ = Γ₁`), and `σ ≠ σ'`
syntactically (only `TyEquiv`). So the arm does **not** go through as-is — a `generalizes_ctxConv`
helper is required. It IS provable, resting on two lemmas — both now **DELIVERED green** in `Scheme.lean`:

- **(A) `Ty.fixes_free_of_subst_eq`** (converse of `subst_eq_of_fixes_free`):
  `Ty.subst σg t = t → ∀ i ∈ Ty.freeVars t, σg i = .var i`. (A free var at a leaf must map to
  itself for the substituted term to match.) ✅
- **(B) `Ty.freeVars_tyEquiv`**: `Ty.TyEquiv σ σ' → ∀ i, i ∈ Ty.freeVars σ ↔ i ∈ Ty.freeVars σ'`
  (`TyEquiv` only swaps distinct row labels and is a congruence — neither adds nor drops type
  variables). ✅

Both compile (`lake build` 1772 + spec unaffected; pure structural inductions, axioms inherited).

**`generalizes_ctxConv` now also DELIVERED green** (`Generalization.lean`, + helper
`substCtx_eq_self_iff`): `TyEquiv σ' σ → Generalizes s (Δ++(x,.mono σ)::Γ) d → Generalizes s
(Δ++(x,.mono σ')::Γ) d`, in the exact `(Δ,Γ,x,σ,σ')` shape `hasType_ctxConv`'s `let_poly` arm
will consume. Proof: from `substCtx σg Γ₁ = Γ₁` extract (A) `σg` fixes `freeVars σ` pointwise; by
(B) it fixes `freeVars σ'`; by `subst_eq_of_fixes_free` (⟸) `subst σg σ' = σ'`. So the
typing-layer obstacle is fully pre-cleared before the cascade.

**Scope impact:** confirms `let_poly` needs *new free-var metatheory* on top of the machine
coupling — so even the typing-layer cascade (before any `Soundness.lean` work) is non-trivial. The
constructor probe was reset (code reverted), but the two foundational lemmas (A)/(B) it surfaced
are **kept and committed** (they are unambiguously needed and standalone-green). `lake build` 1772
+ spec 104/104 green.

## Why this is a milestone slice, not a mechanical edit (unchanged conclusion)
The value-aware `StackWfV`/`MStateWf` change ripples through *every* `.V`-state construction in
both preservation engines, and the new constructor forces B-world arms. The *semantic* core is a
one-liner (the keystone at the push), but the *machine coupling* — carrying a closed `Rdy` + the
`val = w` equality across the lambda-step in a value-aware stack predicate — is the genuine work,
≈ comparable to the `Handle`/`StackSegWf` slice.

## Standalone increments landed; remainder is the coupled cascade

Everything that can be made green *without* the all-or-nothing constructor/`StackWfV` cascade is
now landed and committed: the sharpened design, the import resolution, and the three new lemmas
(`fixes_free_of_subst_eq`, `freeVars_tyEquiv`, `generalizes_ctxConv` + `substCtx_eq_self_iff`).
The remaining `let_poly` work — the `HasType.let_poly` constructor, the value-aware `StackWfV`,
the generalized `StackWf.assign`, and the re-greening of **both** preservation engines — has **no
standalone green increment** (adding the constructor or generalizing `assign` breaks every
induction/inversion across `Typing`/`Generation`/`Substitution`/`Machine`/`Soundness` and the
B-engine at once, so it is committable only when the whole slice is green). That is the dedicated
implementation session; the typing-layer obstacles it would hit are now pre-cleared.

## Status this session
- Sharpened the design: readiness is computed **at the push** (the only context-coherent point);
  the `env ≠ fenv` / `Γc ≠ Γf` mechanism that *defeats pop-time reconstruction* is pinned;
  `StackWfV` (value-aware, recurse-through-`trace`-only) + closed-`Rdy` carriage is the resolved
  shape; the E-side carry is identified with two concrete options to choose at implementation.
- No code changed (the slice is all-or-nothing through the cascade; no standalone green
  increment exists — confirmed). `lake build` 1772 + `lake exe spec` 104/104 still green.
- Next session: execute the checklist; start by choosing the E-side option in step 2.
