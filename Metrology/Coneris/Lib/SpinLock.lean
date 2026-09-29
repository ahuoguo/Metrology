module

public import Metrology.Coneris.Lib.Lock
public import Iris.Instances.Lib.Token

/-!
# A spin lock

Ported from clutch/theories/coneris/lib/spin_lock.v

## Rocq → Lean mapping
* The programs `newlock`, `try_acquire`, `acquire`, `release` keep their names (in
  `Coneris.Lib.SpinLock`; Rocq: `Local Definition`s). They are transcribed with the `cpl`
  notation: `CAS "l" #false #true` is `cas(l, #false, #true)` (= `Snd (CmpXchg ..)`).
* `spin_lockG Σ := LockG { lock_tokG : tokenG Σ }` is the class `spin_lockG GF` with field
  `lock_tokG : TokenG GF` (a local instance in this file, Rocq: `Local Existing Instance`).
* `spin_lockΣ`, `subG_spin_lockΣ`: superseded by iris-lean's `ElemG` instance search
  (as iris-lean's `HeapLang.SpinLock`). A client obtains `spin_lockG GF` from any `TokenG GF`
  by the instance `spin_lockG_of_tokenG`.
* `Let N := nroot .@ "spin_lock"` is the definition `N` (`ndot nroot "spin_lock"`).
* `lock_inv`, `is_lock`, `locked`, `locked_exclusive`, `is_lock_iff`, `newlock_spec`,
  `try_acquire_spec`, `acquire_spec`, `release_spec`: same names.
  `locked_exclusive` is `locked γ ∗ locked γ ⊢ False` (see `Coneris.Lib.Lock`).
* `spin_lock : lock` is a definition (not an instance, as in Rocq), registered by users with
  `attribute [local instance] spin_lock`.

## Added
* `is_lock_persistent`, `locked_timeless` (Rocq infers them when building `spin_lock`), and
  `spin_lockG_of_tokenG`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Coneris.Lib.SpinLock

/-- Rocq: `newlock`. -/
def newlock : val := cpl_val(λ <>, ref(#false))
/-- Rocq: `try_acquire`. -/
def try_acquire : val := cpl_val(λ l, cas(l, #false, #true))
/-- Rocq: `acquire`. -/
def acquire : val :=
  cpl_val(rec acquire l := if &try_acquire l then #() else acquire l)
/-- Rocq: `release`. -/
def release : val := cpl_val(λ l, l ← #false)

/-- Rocq: `spin_lockG`. The CMRA we need. -/
class spin_lockG (GF : BundledGFunctors) where
  lock_tokG : TokenG GF

attribute [instance_reducible] spin_lockG.lock_tokG
attribute [local instance] spin_lockG.lock_tokG

/-- Replaces Rocq's `subG_spin_lockΣ`. -/
instance spin_lockG_of_tokenG {GF : BundledGFunctors} [TokenG GF] : spin_lockG GF := ⟨inferInstance⟩

/-- Rocq: `Let N := nroot .@ "spin_lock"`. -/
def N : Namespace := ndot nroot "spin_lock"

section proof

variable {GF : BundledGFunctors} [conerisGS GF] [spin_lockG GF]

/-- Rocq: `lock_inv`. -/
def lock_inv (γ : GName) (l : Loc) (R : IProp GF) : IProp GF :=
  iprop(∃ b : Bool, l ↦ LitV (LitBool b) ∗ if b then True else token γ ∗ R)

/-- Rocq: `is_lock`. -/
def is_lock (γ : GName) (lk : val) (R : IProp GF) : IProp GF :=
  iprop(∃ l : Loc, ⌜lk = LitV (LitLoc l)⌝ ∧ inv N (lock_inv γ l R))

/-- Rocq: `locked`. -/
def locked (γ : GName) : IProp GF := token γ

/-- Helper (Rocq infers it). -/
instance is_lock_persistent (γ : GName) (lk : val) (R : IProp GF) :
    Persistent (is_lock γ lk R) := by
  unfold is_lock; infer_instance

/-- Helper (Rocq infers it). -/
instance locked_timeless (γ : GName) : Timeless (locked (GF := GF) γ) := by
  unfold locked; infer_instance

omit [conerisGS GF] in
/-- Rocq: `locked_exclusive`. -/
theorem locked_exclusive (γ : GName) : locked γ ∗ locked γ ⊢@{IProp GF} False :=
  token_exclusive γ

/-- Rocq: `is_lock_iff`. -/
theorem is_lock_iff (γ : GName) (lk : val) (R1 R2 : IProp GF) :
    is_lock γ lk R1 ⊢ ▷ □ (R1 ∗-∗ R2) -∗ is_lock γ lk R2 := by
  unfold is_lock lock_inv
  iintro ⟨%l, %H1, #Hinv⟩ #HR
  iexists l
  isplit; itrivial
  iapply inv_iff $$ Hinv
  inext; imodintro
  isplit
  · iintro ⟨%b, Hl, H⟩
    iexists b; iframe Hl
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases H with ⟨$, H⟩
      iapply HR $$ H
    · simp only [↓reduceIte]
      itrivial
  · iintro ⟨%b, Hl, H⟩
    iexists b; iframe Hl
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases H with ⟨$, H⟩
      iapply HR $$ H
    · simp only [↓reduceIte]
      itrivial

/-- Rocq: `newlock_spec`. -/
theorem newlock_spec (R : IProp GF) :
    {{ R }} (App (Val newlock) (Val (LitV LitUnit))) {{ lk γ, RET lk; is_lock γ lk R }} := by
  iintro %Φ HR HΦ
  wp_lam
  wp_alloc l as Hl
  imod token_alloc with ⟨%γ, Hγ⟩
  imod inv_alloc N ⊤ (lock_inv γ l R) $$ [Hl HR Hγ] with #Hinv
  · inext
    unfold lock_inv
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
  imodintro
  iapply HΦ
  unfold is_lock
  iexists l
  isplit
  · ipureintro; rfl
  · iexact Hinv

/-- Rocq: `try_acquire_spec`. -/
theorem try_acquire_spec (γ : GName) (lk : val) (R : IProp GF) :
    {{ is_lock γ lk R }} (App (Val try_acquire) (Val lk))
    {{ b, RET LitV (LitBool b); if b then locked γ ∗ R else True }} := by
  iintro %Φ #Hl HΦ
  unfold is_lock
  icases Hl with ⟨%l, %Heq, #Hinv⟩
  subst Heq
  wp_rec
  wp_bind (CmpXchg _ _ _)
  iinv Hinv with G
  unfold lock_inv
  icases G with ⟨%b, Hl, HR⟩
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_cmpxchg_suc
    icases HR with ⟨Hγ, HR⟩
    imodintro
    isplitl [Hl]
    · inext; iexists true; simp only [↓reduceIte]; iframe
    wp_pures
    iapply HΦ $$ %true
    simp only [↓reduceIte]
    unfold locked
    iframe
  · wp_cmpxchg_fail
    imodintro
    isplitl [Hl]
    · inext; iexists true; simp only [↓reduceIte]; iframe
    wp_pures
    iapply HΦ $$ %false
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial

/-- Rocq: `acquire_spec`. -/
theorem acquire_spec (γ : GName) (lk : val) (R : IProp GF) :
    {{ is_lock γ lk R }} (App (Val acquire) (Val lk)) {{ RET LitV LitUnit; locked γ ∗ R }} := by
  iintro %Φ #Hl HΦ
  iloeb as IH
  wp_rec
  wp_apply try_acquire_spec $$ Hl with %b H
  cases b
  · wp_if
    iapply IH $$ HΦ
  · wp_if
    simp only [↓reduceIte]
    iapply HΦ $$ H

/-- Rocq: `release_spec`. -/
theorem release_spec (γ : GName) (lk : val) (R : IProp GF) :
    {{ is_lock γ lk R ∗ locked γ ∗ R }} (App (Val release) (Val lk))
    {{ RET LitV LitUnit; True }} := by
  iintro %Φ ⟨#Hlock, Hlocked, HR⟩ HΦ
  unfold is_lock
  icases Hlock with ⟨%l, %Heq, #Hinv⟩
  subst Heq
  wp_lam
  iinv Hinv with G
  unfold lock_inv
  icases G with ⟨%b, Hl, -⟩
  wp_store
  isplitr [HΦ]
  · imodintro; inext
    iexists false
    simp only [Bool.false_eq_true, ↓reduceIte]
    unfold locked
    iframe
  · iapply HΦ
    itrivial

end proof

/-- Rocq: `spin_lock`. NOT an instance because users should choose explicitly to use it
(using `attribute [local instance] spin_lock`). -/
@[instance_reducible]
def spin_lock : Lock.lock where
  newlock := newlock
  acquire := acquire
  release := release
  lockG := spin_lockG
  lock_name := GName
  is_lock _ γ lk R := is_lock γ lk R
  locked _ γ := locked γ
  is_lock_persistent _ γ lk R := is_lock_persistent γ lk R
  is_lock_iff _ γ lk R1 R2 := is_lock_iff γ lk R1 R2
  locked_timeless _ γ := locked_timeless γ
  locked_exclusive _ γ := locked_exclusive γ
  newlock_spec _ R := newlock_spec R
  acquire_spec _ γ lk R := acquire_spec γ lk R
  release_spec _ γ lk R := release_spec γ lk R

section test

attribute [local instance] spin_lock

/-- Test (not in Rocq): the generic lock interface, instantiated with `spin_lock`. -/
example {GF : BundledGFunctors} [conerisGS GF] (L : spin_lockG GF) (R : IProp GF) :
    {{ R }} (App (Val Lock.lock.newlock) (Val (LitV LitUnit)))
    {{ lk γ, RET lk; Lock.lock.is_lock L γ lk R }} :=
  Lock.lock.newlock_spec L R

end test

end Coneris.Lib.SpinLock
