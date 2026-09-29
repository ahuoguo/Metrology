module

public import Metrology.Coneris.ProofMode
public import Iris.Instances.Lib.Invariants

/-!
# A general interface for a lock

Ported from clutch/theories/coneris/lib/lock.v (itself taken from the Iris development).

All parameters are implicit (in Rocq), since it is expected that there is only one
`conerisGS` in scope that could possibly apply. To write a library that is generic over the
lock, add a `[lk : lock]` parameter around the code and an `(L : lk.lockG GF)` parameter around
the proofs. To use a particular lock instance, use `attribute [local instance] <lock instance>`
(Rocq: `Local Existing Instance`).

## Rocq → Lean mapping
* `Class lock := Lock {...}` is the Lean `class lock` with the same field names:
  `newlock`, `acquire`, `release`, `lockG`, `lock_name`, `is_lock`, `locked`,
  `is_lock_persistent`, `is_lock_iff`, `locked_timeless`, `locked_exclusive`, `newlock_spec`,
  `acquire_spec`, `release_spec`. As in Rocq, the class does not depend on `Σ` (here `GF`);
  the predicates and specs quantify over `GF` with `[conerisGS GF]`.
* `{L : lockG Σ}` (Rocq, found by type class search since `lockG` is made an
  `Existing Class`) is an explicit argument `(L : lockG GF)`: Lean cannot declare a class
  through a structure projection. (This follows iris-lean's `HeapLang.Lock`.) Inside the
  instances the argument is still a local instance whenever `lockG GF` unfolds to a class
  (e.g. `spin_lockG GF`).
* The `#[global] ... ::` instance fields are fields `is_lock_persistent`/`locked_timeless`,
  re-exported as global instances `lock_is_lock_persistent`/`lock_locked_timeless`.
* `locked_exclusive` is stated as `locked γ ∗ locked γ ⊢ False` (Rocq:
  `locked γ -∗ locked γ -∗ False`, equivalent by currying), as in iris-lean.
* `is_lock_iff` is an entailment `is_lock γ lk R1 ⊢ ▷ □ (R1 ∗-∗ R2) -∗ is_lock γ lk R2`.
* Texan triples are iris-lean's `{{ P }} e {{ x, RET v; Q }}` (Rocq `{{{ P }}} e {{{ x, RET v; Q }}}`),
  at mask `⊤` and stuckness `NotStuck`, as in Rocq.
* `is_lock_contractive` is proved as in iris-lean's `HeapLang/Lib/Lock.lean`.

## Omitted
* `Global Arguments ... : simpl never`, `Hint Mode`, `Hint Extern`: Rocq-specific
  automation settings.
* `is_lock_proper`: iris-lean's OFEs of propositions are compared with `≡`, and non-expansive
  maps respect it; we provide `is_lock_ne` (`OFE.NonExpansive`) instead, as iris-lean does.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.Lock

/-- Rocq: `lock`. -/
class lock where
  -- * Operations
  newlock : val
  acquire : val
  release : val
  -- * Ghost state
  /-- The assumptions about `Σ`. -/
  lockG : BundledGFunctors → Type
  /-- `lock_name` is used to associate `locked` with `is_lock`. -/
  lock_name : Type
  -- * Predicates
  /-- No namespace `N` parameter because we only expose program specs, which anyway have the
  full mask. -/
  is_lock {GF : BundledGFunctors} [conerisGS GF] (L : lockG GF) (γ : lock_name) (lk : val)
    (R : IProp GF) : IProp GF
  locked {GF : BundledGFunctors} [conerisGS GF] (L : lockG GF) (γ : lock_name) : IProp GF
  -- * General properties of the predicates
  is_lock_persistent {GF : BundledGFunctors} [conerisGS GF] (L : lockG GF) γ lk (R : IProp GF) :
    Persistent (is_lock L γ lk R)
  is_lock_iff {GF : BundledGFunctors} [conerisGS GF] (L : lockG GF) γ lk (R1 R2 : IProp GF) :
    is_lock L γ lk R1 ⊢ ▷ □ (R1 ∗-∗ R2) -∗ is_lock L γ lk R2
  locked_timeless {GF : BundledGFunctors} [conerisGS GF] (L : lockG GF) γ :
    Timeless (locked L γ)
  locked_exclusive {GF : BundledGFunctors} [conerisGS GF] (L : lockG GF) γ :
    locked L γ ∗ locked L γ ⊢@{IProp GF} False
  -- * Program specs
  newlock_spec {GF : BundledGFunctors} [conerisGS GF] (L : lockG GF) (R : IProp GF) :
    {{ R }} (App (Val newlock) (Val (LitV LitUnit))) {{ lk γ, RET lk; is_lock L γ lk R }}
  acquire_spec {GF : BundledGFunctors} [conerisGS GF] (L : lockG GF) γ lk (R : IProp GF) :
    {{ is_lock L γ lk R }} (App (Val acquire) (Val lk))
    {{ RET LitV LitUnit; locked L γ ∗ R }}
  release_spec {GF : BundledGFunctors} [conerisGS GF] (L : lockG GF) γ lk (R : IProp GF) :
    {{ is_lock L γ lk R ∗ locked L γ ∗ R }} (App (Val release) (Val lk))
    {{ RET LitV LitUnit; True }}

section lemmas

variable {GF : BundledGFunctors} [conerisGS GF] [lk : lock] (L : lk.lockG GF)

/-- Rocq: `#[global] is_lock_persistent` (the instance). -/
instance lock_is_lock_persistent γ v (R : IProp GF) : Persistent (lk.is_lock L γ v R) :=
  lk.is_lock_persistent L γ v R

/-- Rocq: `#[global] locked_timeless` (the instance). -/
instance lock_locked_timeless γ : Timeless (lk.locked L γ) :=
  lk.locked_timeless L γ

/-- Rocq: `is_lock_contractive`. -/
theorem is_lock_contractive γ v : OFE.Contractive (lk.is_lock L γ v) := by
  rw [contractive_internalEq (PROP := IProp GF)]
  iintro %x₁ %x₂ #HEQ
  iapply prop_ext
  imodintro
  isplit
  · iintro #H
    iapply lock.is_lock_iff $$ H
    iintro !> !>
    irewrite [HEQ]
    · exact ⟨fun _ _ _ h => wandIff_ne.ne h .rfl⟩
    · iapply equiv_wandIff; exact .rfl
  · iintro #H
    iapply lock.is_lock_iff $$ H
    iintro !> !>
    irewrite [HEQ]
    · exact ⟨fun _ _ _ h => wandIff_ne.ne .rfl h⟩
    · iapply equiv_wandIff; exact .rfl

/-- Replaces Rocq's `is_lock_proper` (see the file docstring). -/
instance is_lock_ne γ v : OFE.NonExpansive (lk.is_lock L γ v) :=
  letI _ := is_lock_contractive L γ v
  OFE.ne_of_contractive _

end lemmas

end Coneris.Lib.Lock
