module

public import Metrology.Foxtrot.UnaryRel.UnaryRelTactics

/-!
# Compatibility rules of the unary logical relation of Foxtrot

Ported from clutch/theories/foxtrot/unary_rel/unary_compatibility.v

Compatibility lemmas for the unary "refinement" judgement `REL e : A` (`= WP e {{ A }}`,
namespace `Foxtrot.UnaryRel`).

## Rocq → Lean map
`refines_pair`, `refines_injl`, `refines_injr`, `refines_app`, `refines_seq`, `refines_pack`,
`refines_forall`, `refines_store`, `refines_load`, `refines_rand_tape`, `refines_rand_unit`,
`refines_cmpxchg_ref`, `refines_xchg`: same names and argument order.
* Rocq's `lrel_scope` notations are written with the constructors: `A * B` is `lrel_prod A B`,
  `A + B` is `lrel_sum A B`, `A → B` is `lrel_arr A B`, `ref A` is `lrel_ref A`, `()` is
  `lrel_unit`, `∃ A, C A` is `lrel_exists C`, `∀ A, C A` is `lrel_forall C`.
* Expressions: `(e1, e2)` is `Pair e1 e2`, `e1;; e2` is `Seq e1 e2`, `λ: <>, e` (a value) is
  `Val (RecV BAnon BAnon e)`, `e1 <- e2` is `Store e1 e2`, `!e` is `Load e`, `rand(e2) e1` is
  `Rand e1 e2`, `rand e` is `Rand e (Val #())`.
* The local Ltac `rel_bind_ap e IH v Hv` is a local macro (`rel_bind_l e; iapply refines_bind $$
  IH; iintro %v Hv; rel_finish`). The local `unfold_rel` is `unfold_rel` of `UnaryModel`.

## Deviations
* Rocq's `P -∗ Q -∗ R` statements are entailments `P ⊢ Q -∗ R`.
* `wp_apply (wp_wand with "[$]")` is `wp_apply wp_wand $$ H`; `iInv` is iris-lean's `iinv`
  (through the `ElimAcc` instances of `Foxtrot.Weakestpre`).
* `refines_cmpxchg_ref`, `refines_xchg`: Rocq wraps the atomic step in `iApply wp_pupd` (a
  leftover of the commented-out right-hand-side step `tp_cmpxchg_suc`/`tp_xchg`) and then
  removes the `pupd` again with `iModIntro`; since there is no right-hand side, this detour is
  omitted. `rewrite -(fill_empty ..); iApply refines_atomic_l` is an `iapply` of
  `refines_atomic_l _ []` restated at the bare expression.
* `refines_rand_tape`: `destruct (decide (N = M))` is `by_cases`; the wrong-bound case uses
  `wp_rand_tape_wrong_bound` with the tape bound `N` and the sampling bound `M`.

## Omitted
* The commented-out Rocq code (`value_case`, `rel_store_l_atomic`, the commented RHS steps).
-/

@[expose] public section

noncomputable section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.UnaryRel

section compatibility

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: the local tactic `rel_bind_ap e1 IH v Hvs`: bind `e1`, apply `refines_bind` with `IH`
and introduce the resulting value `v` and its interpretation `Hvs`. -/
local macro "rel_bind_ap " e:term:max ppSpace IH:ident ppSpace v:ident ppSpace Hv:introPat :
    tactic => `(tactic| focus
      rel_bind_l $e
      iapply refines_bind $$ $IH:ident
      iintro %$v:ident $Hv:introPat
      rel_finish)

/-- Rocq: `refines_pair`. -/
theorem refines_pair (e1 e2 : expr) (A B : lrel GF) :
    (REL e1 : A) ⊢ (REL e2 : B) -∗ REL Pair e1 e2 : lrel_prod A B := by
  unfold_rel
  iintro H1 H2
  wp_bind e2
  wp_apply wp_wand $$ H2
  iintro %v2 H2
  wp_bind e1
  wp_apply wp_wand $$ H1
  iintro %v1 H1
  wp_pures
  imodintro
  unfold lrel_prod
  iexists v1, v2
  isplitr
  · ipureintro; rfl
  · iframe H1 H2

/-- Rocq: `refines_injl`. -/
theorem refines_injl (e : expr) (τ1 τ2 : lrel GF) :
    (REL e : τ1) ⊢ REL InjL e : lrel_sum τ1 τ2 := by
  unfold_rel
  iintro IH
  wp_bind e
  wp_apply wp_wand $$ IH
  iintro %v Hv
  wp_pures
  imodintro
  unfold lrel_sum
  iexists v
  ileft
  isplitr
  · ipureintro; rfl
  · iexact Hv

/-- Rocq: `refines_injr`. -/
theorem refines_injr (e : expr) (τ1 τ2 : lrel GF) :
    (REL e : τ2) ⊢ REL InjR e : lrel_sum τ1 τ2 := by
  unfold_rel
  iintro IH
  wp_bind e
  wp_apply wp_wand $$ IH
  iintro %v Hv
  wp_pures
  imodintro
  unfold lrel_sum
  iexists v
  iright
  isplitr
  · ipureintro; rfl
  · iexact Hv

/-- Rocq: `refines_app`. -/
theorem refines_app (e1 e2 : expr) (A B : lrel GF) :
    (REL e1 : lrel_arr A B) ⊢ (REL e2 : A) -∗ REL App e1 e2 : B := by
  unfold_rel
  iintro IH1 IH2
  wp_bind e2
  wp_apply wp_wand $$ IH2
  iintro %v2 H2
  wp_bind e1
  wp_apply wp_wand $$ IH1
  iintro %v1 H1
  unfold lrel_arr
  icases H1 with #H1
  ihave H := H1 $$ H2
  unfold_rel
  iexact H

/-- Rocq: `refines_seq`. -/
theorem refines_seq (A : lrel GF) (e1 e2 : expr) (B : lrel GF) :
    (REL e1 : A) ⊢ (REL e2 : B) -∗ REL Seq e1 e2 : B := by
  unfold_rel
  iintro IH1 IH2
  wp_bind e1
  wp_apply wp_wand $$ IH1
  iintro %v _
  wp_pures
  iexact IH2

/-- Rocq: `refines_pack`. -/
theorem refines_pack (A : lrel GF) (e : expr) (C : lrel GF → lrel GF) :
    (REL e : C A) ⊢ REL e : lrel_exists C := by
  unfold_rel
  iintro H
  iapply wp_wand $$ H
  iintro %v Hv
  unfold lrel_exists
  iexists A
  iexact Hv

/-- Rocq: `refines_forall`. -/
theorem refines_forall (e : expr) (C : lrel GF → lrel GF) :
    □ (∀ A, REL e : C A) ⊢ REL Val (RecV BAnon BAnon e) : lrel_forall C := by
  iintro #H
  rel_values
  imodintro
  unfold lrel_forall lrel_arr lrel_unit
  iintro %A !> %v1 %hv
  subst hv
  unfold_rel
  wp_pures
  iapply H

/-- Rocq: `refines_store`. -/
theorem refines_store (e1 e2 : expr) (A : lrel GF) :
    (REL e1 : lrel_ref A) ⊢ (REL e2 : A) -∗ REL Store e1 e2 : lrel_unit := by
  unfold_rel
  iintro IH1 IH2
  wp_bind e2
  wp_apply wp_wand $$ IH2
  iintro %v2 HA
  wp_bind e1
  wp_apply wp_wand $$ IH1
  iintro %v1 #H
  unfold lrel_ref
  icases H with ⟨%l, %hl, #Hinv⟩
  subst hl
  iinv Hinv with ⟨%w, >Hl, -⟩ Hclose
  wp_store
  imod Hclose $$ [HA Hl]
  · inext
    iexists v2
    iframe HA Hl
  imodintro
  unfold lrel_unit
  ipureintro
  rfl

/-- Rocq: `refines_load`. -/
theorem refines_load (e : expr) (A : lrel GF) :
    (REL e : lrel_ref A) ⊢ REL Load e : A := by
  iintro H
  unfold_rel
  wp_bind e
  wp_apply wp_wand $$ H
  iintro %v #H
  unfold lrel_ref
  icases H with ⟨%l, %hl, #Hinv⟩
  subst hl
  iinv Hinv with ⟨%w, >Hl, #Hw⟩ Hclose
  wp_load
  imod Hclose $$ [Hl]
  · inext
    iexists w
    iframe Hl Hw
  imodintro
  iexact Hw

/-- Rocq: `refines_rand_tape`. -/
theorem refines_rand_tape (e1 e2 : expr) :
    (REL e1 : (lrel_nat : lrel GF)) ⊢ (REL e2 : lrel_tape) -∗ REL Rand e1 e2 : lrel_nat := by
  unfold_rel
  iintro IH1 IH2
  wp_bind e2
  wp_apply wp_wand $$ IH2
  iintro %v2 HA
  wp_bind e1
  wp_apply wp_wand $$ IH1
  iintro %v1 HA'
  unfold lrel_nat lrel_tape
  icases HA' with ⟨%M, %hM⟩
  subst hM
  icases HA with ⟨%α, %N, %hα, #Hinv⟩
  subst hα
  iinv Hinv with >Hα Hclose
  ihave Hα := empty_to_tapeN α N $$ Hα
  by_cases hNM : N = M
  · subst hNM
    wp_apply wp_rand_tape_empty N (N : ℤ) α (by simp) $$ Hα with %n ⟨Ht, %hn⟩
    imod Hclose $$ [Ht]
    · inext
      iapply tapeN_to_empty $$ Ht
    imodintro
    iexists n
    ipureintro
    rfl
  · wp_apply wp_rand_tape_wrong_bound M N (M : ℤ) α [] (by simp) (Ne.symm hNM) $$ Hα
      with %n ⟨Ht, %hn⟩
    imod Hclose $$ [Ht]
    · inext
      iapply tapeN_to_empty $$ Ht
    imodintro
    iexists n
    ipureintro
    rfl

/-- Rocq: `refines_rand_unit`. -/
theorem refines_rand_unit (e : expr) :
    (REL e : (lrel_nat : lrel GF)) ⊢ REL Rand e (Val (LitV LitUnit)) : lrel_nat := by
  unfold_rel
  iintro H
  wp_bind e
  wp_apply wp_wand $$ H
  iintro %v HA
  unfold lrel_nat
  icases HA with ⟨%M, %hM⟩
  subst hM
  wp_apply wp_rand M (M : ℤ) (by simp) with %n %hn
  · itrivial
  iexists n
  ipureintro
  rfl

/-- Rocq: `refines_cmpxchg_ref`. -/
theorem refines_cmpxchg_ref (A : lrel GF) (e1 e2 e3 : expr) :
    (REL e1 : lrel_ref (lrel_ref A)) ⊢ (REL e2 : lrel_ref A) -∗ (REL e3 : lrel_ref A) -∗
      REL CmpXchg e1 e2 e3 : lrel_prod (lrel_ref A) lrel_bool := by
  iintro IH1 IH2 IH3
  rel_bind_ap e3 IH3 v3 #IH3
  rel_bind_ap e2 IH2 v2 #IH2
  rel_bind_ap e1 IH1 v1 #IH1
  unfold lrel_ref
  icases IH1 with ⟨%l1, %hl1, #Hinv⟩
  subst hl1
  icases IH2 with ⟨%r1, %hr1, #Hr⟩
  subst hr1
  have h : _ ⊢ REL CmpXchg (Val (LitV (LitLoc l1))) (Val (LitV (LitLoc r1))) (Val v3) :
      lrel_prod (lrel_ref A) lrel_bool :=
    refines_atomic_l (⊤ \ ↑(logN.@ l1)) []
      (CmpXchg (Val (LitV (LitLoc l1))) (Val (LitV (LitLoc r1))) (Val v3))
      (lrel_prod (lrel_ref A) lrel_bool)
  unfold lrel_ref at h
  iapply h
  iinv Hinv with ⟨%v1, Hl1, #Hv⟩ Hclose
  imodintro
  by_cases hv : v1 = LitV (LitLoc r1)
  · subst hv
    wp_cmpxchg_suc
    imod Hclose $$ [Hl1]
    · inext
      iexists v3
      iframe Hl1 IH3
    imodintro
    rel_finish
    rel_values
    unfold lrel_prod lrel_bool
    iexists (LitV (LitLoc r1)), (LitV (LitBool true))
    isplitr
    · ipureintro; rfl
    isplitl
    · iexact Hv
    · iexists true
      ipureintro; rfl
  · wp_cmpxchg_fail
    imod Hclose $$ [Hl1]
    · inext
      iexists v1
      iframe Hl1 Hv
    imodintro
    rel_finish
    rel_values
    unfold lrel_prod lrel_bool
    iexists v1, (LitV (LitBool false))
    isplitr
    · ipureintro; rfl
    isplitl
    · iexact Hv
    · iexists false
      ipureintro; rfl

/-- Rocq: `refines_xchg`. -/
theorem refines_xchg (e1 e2 : expr) (A : lrel GF) :
    (REL e1 : lrel_ref A) ⊢ (REL e2 : A) -∗ REL Xchg e1 e2 : A := by
  iintro IH1 IH2
  rel_bind_ap e2 IH2 w IH2
  rel_bind_ap e1 IH1 v IH1
  unfold lrel_ref
  icases IH1 with ⟨%l, %hl, #Hinv⟩
  subst hl
  have h : _ ⊢ REL Xchg (Val (LitV (LitLoc l))) (Val w) : A :=
    refines_atomic_l (⊤ \ ↑(logN.@ l)) [] (Xchg (Val (LitV (LitLoc l))) (Val w)) A
  iapply h
  iinv Hinv with ⟨%v, Hv1, #Hv⟩ Hclose
  imodintro
  wp_xchg
  imod Hclose $$ [Hv1 IH2]
  · inext
    iexists w
    iframe Hv1 IH2
  imodintro
  rel_finish
  rel_values

end compatibility

end Foxtrot.UnaryRel
