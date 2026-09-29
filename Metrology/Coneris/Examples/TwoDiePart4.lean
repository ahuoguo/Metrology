module

public import Metrology.Coneris.Examples.TwoDiePart3

/-!
# Two dice: `complex_parallel_add_spec'`

Ported from clutch/theories/coneris/examples/two_die.v (fourth part: the lemma
`complex_parallel_add_spec'` of section `complex'`)

See `Coneris.Examples.TwoDie` for the Rocq → Lean map, the deviations and the omissions of
the whole Rocq file.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang
open Coneris Coneris.Lib.Spawn Coneris.Lib.Par
open Iris.ExclAuth

namespace Coneris.Examples.TwoDie

attribute [local instance] Classical.propDecidable

open T

section complex'

variable {GF : BundledGFunctors} [conerisGS GF] [spawnG GF] [ElemG GF (excl_authF T)]

/-- Rocq: `complex_parallel_add_spec'`. -/
theorem complex_parallel_add_spec' :
    {{ ↯ (1 / 36) }} two_die_prog'
    {{ (n : ℕ), RET LitV (LitInt (n : ℤ)); (⌜0 < n⌝ : IProp GF) }} := by
  iintro %Φ Herr HΦ
  imod ghost_var_allocT S0 with ⟨%γ1, Hauth1, Hfrag1⟩
  imod ghost_var_allocT S0 with ⟨%γ2, Hauth2, Hfrag2⟩
  unfold two_die_prog'
  wp_alloc l as Hl
  wp_pures
  imod inv_alloc nroot ⊤ (parallel_add_inv' γ1 γ2 l) $$ [Hauth1 Hauth2 Herr Hl] with #I
  · inext
    unfold parallel_add_inv'
    iexists S0, S0, 0
    rw [added_1_S0, show one_positive S0 S0 = false by simp [one_positive, sampled]]
    simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    iframe
    isplitl []
    · itrivial
    iexists 0
    rw [six_rpow_zero_sub_two]
    iframe
    ipureintro
    simp [sampled]
  wp_apply wp_par' (fun _ => iprop(∃ n : ℕ, own_frag γ1 (S2 n)))
    (fun _ => iprop(∃ n : ℕ, own_frag γ2 (S2 n))) $$ [Hfrag1] [Hfrag2]
  · unfold parallel_add_inv'
    wp_bind (Rand _ _)
    iinv I with ⟨%s1, %s2, %n, >Hauth1, >Hauth2, >Hl, >H, >Herr⟩ Hclose
    ihave %Heq := ghost_var_agreeT $$ Hauth1 Hfrag1
    subst Heq
    rw [added_1_S0, Bool.false_or]
    cases H1 : one_positive S0 s2
    · -- no positive sample yet
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herr with ⟨%flip_num, Herr, %Hflip⟩
      simp only [show sampled S0 = none from rfl, reduceCtorEq, decide_false, Bool.toNat_false,
        zero_add] at Hflip
      subst Hflip
      wp_apply wp_couple_rand_adv_comp1' 5 5 _
        (fun x => if (x : ℕ) = 0
          then (6 : ℝ≥0∞) ^ (((decide (sampled s2 = some 0)).toNat : ℝ) - 2 + 1) else 0)
        rfl (six_rpow_mean _) $$ Herr with %x Herr
      by_cases H2 : (x : ℕ) = 0
      · imod ghost_var_updateT γ1 (S2 0) _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
        have H3 : one_positive (S2 0) s2 = false := by
          rw [Bool.eq_false_iff] at H1 ⊢
          intro h
          obtain ⟨m, hm, (hm' | hm')⟩ := (one_positive_eq _ _).1 h
          · simp only [sampled, Option.some.injEq] at hm'; omega
          · exact H1 ((one_positive_eq _ _).2 ⟨m, hm, Or.inr hm'⟩)
        imod Hclose $$ [Hauth1 Hauth2 Hl H Herr]
        · inext
          iexists S2 0, s2, n
          rw [added_1_S2, H3]
          simp only [gt_iff_lt, lt_self_iff_false, decide_false, Bool.false_or, H2,
            Bool.false_eq_true, ↓reduceIte]
          iframe
          iexists 1 + (decide (sampled s2 = some 0)).toNat
          isplitl
          · iapply ErrorCredit.ext _ $$ Herr
            push_cast
            ring_nf
          · ipureintro
            simp [sampled]
        imodintro
        wp_pures
        rw [decide_eq_false (by omega)]
        wp_pures
        iexists 0
        iexact Hfrag1
      · have hx : (x : ℕ) > 0 := Nat.pos_of_ne_zero H2
        imod ghost_var_updateT γ1 (S1 x hx) _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
        have H3 : one_positive (S1 x hx) s2 = true :=
          (one_positive_eq _ _).2 ⟨x, hx, Or.inl rfl⟩
        imod Hclose $$ [Hauth1 Hauth2 Hl H Herr]
        · inext
          iexists S1 x hx, s2, n
          rw [added_1_S1, H3]
          simp only [Bool.false_or, H2, ↓reduceIte]
          iframe
        imodintro
        wp_pures
        rw [decide_eq_true (by omega)]
        wp_pures
        iapply complex_parallel_add_spec'_faa1 γ1 γ2 l x hx
        unfold parallel_add_inv'
        isplitr
        · iexact I
        · iexact Hfrag1
    · -- the other thread already sampled a positive number
      simp only [↓reduceIte]
      wp_apply wp_rand 5 5 rfl $$ []
      · itrivial
      iintro %x -
      by_cases H2 : (x : ℕ) = 0
      · imod ghost_var_updateT γ1 (S2 0) _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
        have H3 : one_positive (S2 0) s2 = true := by
          obtain ⟨m, hm, (hm' | hm')⟩ := (one_positive_eq _ _).1 H1
          · simp [sampled] at hm'
          · exact (one_positive_eq _ _).2 ⟨m, hm, Or.inr hm'⟩
        imod Hclose $$ [Hauth1 Hauth2 Hl H Herr]
        · inext
          iexists S2 0, s2, n
          rw [added_1_S2, H3]
          simp only [gt_iff_lt, lt_self_iff_false, decide_false, Bool.false_or, ↓reduceIte]
          iframe
        imodintro
        wp_pures
        rw [decide_eq_false (by omega)]
        wp_pures
        iexists 0
        iexact Hfrag1
      · have hx : (x : ℕ) > 0 := Nat.pos_of_ne_zero H2
        imod ghost_var_updateT γ1 (S1 x hx) _ _ $$ Hauth1 Hfrag1 with ⟨Hauth1, Hfrag1⟩
        have H3 : one_positive (S1 x hx) s2 = true :=
          (one_positive_eq _ _).2 ⟨x, hx, Or.inl rfl⟩
        imod Hclose $$ [Hauth1 Hauth2 Hl H Herr]
        · inext
          iexists S1 x hx, s2, n
          rw [added_1_S1, H3]
          simp only [Bool.false_or, ↓reduceIte]
          iframe
        imodintro
        wp_pures
        rw [decide_eq_true (by omega)]
        wp_pures
        iapply complex_parallel_add_spec'_faa1 γ1 γ2 l x hx
        unfold parallel_add_inv'
        isplitr
        · iexact I
        · iexact Hfrag1
  · unfold parallel_add_inv'
    wp_bind (Rand _ _)
    iinv I with ⟨%s1, %s2, %n, >Hauth1, >Hauth2, >Hl, >H, >Herr⟩ Hclose
    ihave %Heq := ghost_var_agreeT $$ Hauth2 Hfrag2
    subst Heq
    rw [added_1_S0, Bool.or_false]
    cases H1 : one_positive s1 S0
    · -- no positive sample yet
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Herr with ⟨%flip_num, Herr, %Hflip⟩
      simp only [show sampled S0 = none from rfl, reduceCtorEq, decide_false, Bool.toNat_false,
        add_zero] at Hflip
      subst Hflip
      wp_apply wp_couple_rand_adv_comp1' 5 5 _
        (fun x => if (x : ℕ) = 0
          then (6 : ℝ≥0∞) ^ (((decide (sampled s1 = some 0)).toNat : ℝ) - 2 + 1) else 0)
        rfl (six_rpow_mean _) $$ Herr with %x Herr
      by_cases H2 : (x : ℕ) = 0
      · imod ghost_var_updateT γ2 (S2 0) _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
        have H3 : one_positive s1 (S2 0) = false := by
          rw [Bool.eq_false_iff] at H1 ⊢
          intro h
          obtain ⟨m, hm, (hm' | hm')⟩ := (one_positive_eq _ _).1 h
          · exact H1 ((one_positive_eq _ _).2 ⟨m, hm, Or.inl hm'⟩)
          · simp only [sampled, Option.some.injEq] at hm'; omega
        imod Hclose $$ [Hauth1 Hauth2 Hl H Herr]
        · inext
          iexists s1, S2 0, n
          rw [added_1_S2, H3]
          simp only [gt_iff_lt, lt_self_iff_false, decide_false, Bool.or_false, H2,
            Bool.false_eq_true, ↓reduceIte]
          iframe
          iexists (decide (sampled s1 = some 0)).toNat + 1
          isplitl
          · iapply ErrorCredit.ext _ $$ Herr
            push_cast
            ring_nf
          · ipureintro
            simp [sampled]
        imodintro
        wp_pures
        rw [decide_eq_false (by omega)]
        wp_pures
        iexists 0
        iexact Hfrag2
      · have hx : (x : ℕ) > 0 := Nat.pos_of_ne_zero H2
        imod ghost_var_updateT γ2 (S1 x hx) _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
        have H3 : one_positive s1 (S1 x hx) = true :=
          (one_positive_eq _ _).2 ⟨x, hx, Or.inr rfl⟩
        imod Hclose $$ [Hauth1 Hauth2 Hl H Herr]
        · inext
          iexists s1, S1 x hx, n
          rw [added_1_S1, H3]
          simp only [Bool.or_false, H2, ↓reduceIte]
          iframe
        imodintro
        wp_pures
        rw [decide_eq_true (by omega)]
        wp_pures
        iapply complex_parallel_add_spec'_faa2 γ1 γ2 l x hx
        unfold parallel_add_inv'
        isplitr
        · iexact I
        · iexact Hfrag2
    · -- the other thread already sampled a positive number
      simp only [↓reduceIte]
      wp_apply wp_rand 5 5 rfl $$ []
      · itrivial
      iintro %x -
      by_cases H2 : (x : ℕ) = 0
      · imod ghost_var_updateT γ2 (S2 0) _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
        have H3 : one_positive s1 (S2 0) = true := by
          obtain ⟨m, hm, (hm' | hm')⟩ := (one_positive_eq _ _).1 H1
          · exact (one_positive_eq _ _).2 ⟨m, hm, Or.inl hm'⟩
          · simp [sampled] at hm'
        imod Hclose $$ [Hauth1 Hauth2 Hl H Herr]
        · inext
          iexists s1, S2 0, n
          rw [added_1_S2, H3]
          simp only [gt_iff_lt, lt_self_iff_false, decide_false, Bool.or_false, ↓reduceIte]
          iframe
        imodintro
        wp_pures
        rw [decide_eq_false (by omega)]
        wp_pures
        iexists 0
        iexact Hfrag2
      · have hx : (x : ℕ) > 0 := Nat.pos_of_ne_zero H2
        imod ghost_var_updateT γ2 (S1 x hx) _ _ $$ Hauth2 Hfrag2 with ⟨Hauth2, Hfrag2⟩
        have H3 : one_positive s1 (S1 x hx) = true :=
          (one_positive_eq _ _).2 ⟨x, hx, Or.inr rfl⟩
        imod Hclose $$ [Hauth1 Hauth2 Hl H Herr]
        · inext
          iexists s1, S1 x hx, n
          rw [added_1_S1, H3]
          simp only [Bool.or_false, ↓reduceIte]
          iframe
        imodintro
        wp_pures
        rw [decide_eq_true (by omega)]
        wp_pures
        iapply complex_parallel_add_spec'_faa2 γ1 γ2 l x hx
        unfold parallel_add_inv'
        isplitr
        · iexact I
        · iexact Hfrag2
  · iintro %v1 %v2 ⟨⟨%n1, Hfrag1⟩, ⟨%n2, Hfrag2⟩⟩
    inext
    wp_pures
    unfold parallel_add_inv'
    iinv I with ⟨%s1, %s2, %n, >Hauth1, >Hauth2, >Hl, >H, >Herr⟩ Hclose
    ihave %Heq1 := ghost_var_agreeT $$ Hauth1 Hfrag1
    ihave %Heq2 := ghost_var_agreeT $$ Hauth2 Hfrag2
    subst Heq1 Heq2
    wp_load
    ihave %Hn : iprop(⌜0 < n⌝) $$ [H Herr]
    · cases hA : added_1 (S2 n1) || added_1 (S2 n2)
      · simp only [Bool.or_eq_false_iff, added_1_S2, decide_eq_false_iff_not, gt_iff_lt,
          not_lt, Nat.le_zero] at hA
        obtain ⟨rfl, rfl⟩ := hA
        rw [show one_positive (S2 0) (S2 0) = false by simp [one_positive, sampled]]
        simp only [Bool.false_eq_true, ↓reduceIte]
        icases Herr with ⟨%flip_num, Herr, %Hflip⟩
        simp only [sampled, decide_true, Bool.toNat_true] at Hflip
        subst Hflip
        iexfalso
        iapply ErrorCredit.contradict (le_of_eq six_rpow_two_sub_two.symm) $$ Herr
      · simp only [↓reduceIte]
        iexact H
    imod Hclose $$ [Hauth1 Hauth2 Hl H Herr]
    · inext
      iexists S2 n1, S2 n2, n
      iframe
    imodintro
    iapply HΦ
    ipureintro
    exact Hn

end complex'

end Coneris.Examples.TwoDie
