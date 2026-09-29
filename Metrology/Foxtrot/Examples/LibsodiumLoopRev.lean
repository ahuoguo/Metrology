module

public import Metrology.Foxtrot.Examples.Libsodium

/-!
# `randombytes_uniform`: `rbu_rem_tape ≤ctx≤ randombytes_uniform`

Ported from clutch/theories/foxtrot/examples/libsodium.v (part 2e: the main goal of
`ideal_refines_randombytes_uniform`).

The rejection-sampling loop is now on the RHS. If `MAX mod n = 0` there is no rejection and
the LHS tape is coupled exactly with the RHS sample (`pupd_couple_tape_rand`). Otherwise an
error credit `↯ ε` (`pupd_epsilon_err`) is amplified by the induction principle
`ErrorCredit.Induction.simple` (Rocq: `ec_ind_simpl`) with factor `MAX / (MAX mod n)`: each RHS
sample is coupled with a presampling on the LHS tape by
`pupd_couple_fragmented_tape_rand_inj_rev'`, which, on rejection, multiplies the credit by
exactly this factor.

## Rocq → Lean map
* `rem_tape_refines_randombytes_uniform` (Rocq: the remaining goal).
* `ec_ind_simpl` is `ErrorCredit.Induction.simple` (with `k : ℝ≥0`); the factor
  `(MAX / (MAX - (MAX - MAX mod n)))%R` is `(MAX : ℝ≥0) / (MAX % n : ℝ≥0)` (the equation
  with the factor of `pupd_couple_fragmented_tape_rand_inj_rev'` is `rej_coeff_eq`, the side
  condition is `rej_coeff_gt_one`).

## Deviations
* Rocq's `iRevert (z) "Hl Hspec Hα"` (with `z` from `remember 0%Z`) is
  `irevert Hl Hspec Hα; generalize (0 : ℤ) = z; irevert %z`.
* Rocq's `destruct (MAX mod n) eqn:Heqn` is `by_cases hr : MAX % n = 0`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.BinaryRel

namespace Foxtrot.Examples.Libsodium

theorem rem_tape_refines_randombytes_uniform (MAX : ℕ) :
    (∅ : varmap type) ⊨ Val (rbu_rem_tape MAX) ≤ctx≤ Val (randombytes_uniform MAX) :
      TArrow TNat TNat := by
  apply start
  intro _ n K j
  iintro Hspec
  unfold rbu_rem_tape randombytes_uniform
  wp_pures
  tp_pures j
  by_cases h : MAX ≤ n
  · simp only [h, decide_true]
    tp_pures j
    wp_pures
    iexists 0
    iframe Hspec
    ipureintro
    rfl
  · simp only [h, decide_false]
    tp_pures j
    wp_pures
    by_cases hn0 : n = 0
    · subst hn0
      simp only [decide_true, show (0 : ℕ) ≤ 1 from Nat.zero_le _]
      tp_pures j
      wp_pures
      iexists 0
      iframe Hspec
      ipureintro
      rfl
    by_cases hn1 : n = 1
    · subst hn1
      simp only [decide_true, show ¬ (1 : ℕ) = 0 from one_ne_zero, decide_false, le_refl]
      tp_pures j
      wp_pures
      wp_alloctape α as Hα
      wp_pures
      wp_apply wp_rand_tape_empty _ _ α rfl $$ Hα with %m ⟨-, -⟩
      wp_pures
      iexists 0
      iframe Hspec
      ipureintro
      simp
    have hn2 : ¬ n ≤ 1 := by omega
    simp only [hn0, hn2, decide_false]
    tp_pures j
    wp_pures
    tp_alloc j as l Hl
    tp_pure j
    tp_pure j
    tp_pure j
    have hn : 0 < n := by omega
    have hnM : n < MAX := by omega
    obtain ⟨h1, h2, h3⟩ := rej_facts MAX n hn hnM
    have e1 : Int.tmod (MAX : ℤ) (n : ℤ) = ((MAX % n : ℕ) : ℤ) := (Int.ofNat_tmod _ _).symm
    have e2 : ((MAX : ℤ) - ((MAX % n : ℕ) : ℤ) - 1) = ((MAX - MAX % n - 1 : ℕ) : ℤ) := by
      omega
    rw [e1, e2]
    wp_alloctape α as Hα
    wp_pures
    rw [e1, e2]
    try simp only [Int.toNat_natCast]
    by_cases hr : MAX % n = 0
    · rw [hr]
      try simp only [Nat.sub_zero]
      tp_pures j
      tp_bind j (Rand _ _)
      imod pupd_couple_tape_rand (MAX - 1) id Function.bijective_id _ ⊤ α _ [] j
        (Int.toNat_natCast _).symm (fun _ h => h) $$ Hα Hspec with ⟨%k, Hα, Hspec, %Hk⟩
      simp only [id]
      tp_store j
      tp_pures j
      tp_load j
      tp_pures j
      simp only [show ¬ ((k : ℤ) < 0) by omega, decide_false]
      tp_pures j
      tp_load j
      tp_pures j
      rw [List.nil_append]
      wp_randtape as Hα
      wp_pures
      simp only [← Int.ofNat_tmod]
      iexists k % n
      iframe Hspec
      ipureintro
      rfl
    have hr0 : 0 < MAX % n := Nat.pos_of_ne_zero hr
    have hrM : MAX % n < MAX := by omega
    imod pupd_epsilon_err ⊤ with ⟨%ε, %Hε, Herr⟩
    irevert Hl Hspec Hα
    generalize (0 : ℤ) = z
    irevert %z
    irevert Herr
    iapply ErrorCredit.Induction.simple Hε (rej_coeff_gt_one MAX (MAX % n) hr0 hrM)
    iintro !> ⟨IH, Herr⟩ %z Hl Hspec Hα
    tp_pures j
    tp_bind j (Rand _ _)
    imod pupd_couple_fragmented_tape_rand_inj_rev' (M := MAX - 1) (N := MAX - MAX % n - 1)
      (rej_f MAX n) (rej_f_inj MAX n) [] α j _ ⊤ ε (by omega) (rej_f_dom MAX n hn hnM) $$
      Hα Herr Hspec with ⟨%x, %Hx, Hspec, H⟩
    icases H with (⟨%m, %Hm, %Hfm, Hα⟩ | ⟨%Hcontra, Hα, Herr⟩)
    · -- accepted
      subst Hfm
      obtain ⟨Ha1, Ha2⟩ := rej_f_accept MAX n hn hnM m Hm
      have hlt : ¬ ((rej_f MAX n m : ℕ) : ℤ) < (MAX : ℤ) % (n : ℤ) := by
        rw [← Int.natCast_mod]; exact_mod_cast Nat.not_lt.2 Ha1
      tp_store j
      tp_pures j
      tp_load j
      tp_pures j
      simp only [hlt, decide_false]
      tp_pures j
      tp_load j
      tp_pures j
      rw [List.nil_append]
      wp_randtape as Hα
      wp_pures
      simp only [← Int.ofNat_tmod]
      rw [Ha2]
      iexists m % n
      iframe Hspec
      ipureintro
      rfl
    · -- rejected
      have hlt : (x : ℤ) < (MAX : ℤ) % (n : ℤ) := by
        rw [← Int.natCast_mod]; exact_mod_cast rej_f_reject MAX n hn hnM x Hx Hcontra
      rw [rej_coeff_eq MAX (MAX % n) hr0 hrM]
      tp_store j
      tp_pures j
      tp_load j
      tp_pures j
      simp only [hlt, _root_.decide_true]
      tp_pure j
      iapply IH $$ Herr %_ Hl Hspec Hα

end Foxtrot.Examples.Libsodium
