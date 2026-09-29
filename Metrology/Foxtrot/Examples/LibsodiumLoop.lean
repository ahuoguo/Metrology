module

public import Metrology.Foxtrot.Examples.Libsodium

/-!
# `randombytes_uniform`: `randombytes_uniform ≤ctx≤ rbu_rem`

Ported from clutch/theories/foxtrot/examples/libsodium.v (part 2c: the main goal of
`randombytes_uniform_refines_ideal`).

The rejection-sampling loop on the LHS is related by Löb induction to the single sample of
the RHS: each LHS `rand (MAX - 1)` is coupled with the RHS `rand (MAX - MAX mod n - 1)` by the
fragmented coupling `wp_couple_fragmented_rand_rand_inj` along the injection `rej_f`; if the
LHS sample is rejected, the RHS sample is still pending and the loop continues.

## Rocq → Lean map
* `randombytes_uniform_refines_rem` (Rocq: the remaining goal).

## Deviations
* Rocq's `remember 0%Z as z; iLöb as "IH" forall (z)` is `generalize (0 : ℤ) = z;
  iloeb as IH generalizing %z Hl Hspec`.
* The arithmetic of the accept/reject branches is in `rej_f_accept`/`rej_f_reject`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.BinaryRel

namespace Foxtrot.Examples.Libsodium

theorem randombytes_uniform_refines_rem (MAX : ℕ) :
    (∅ : varmap type) ⊨ Val (randombytes_uniform MAX) ≤ctx≤ Val (rbu_rem MAX) :
      TArrow TNat TNat := by
  apply start
  intro _ n K j
  iintro Hspec
  unfold randombytes_uniform rbu_rem
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
      tp_bind j (Rand _ _)
      imod pupd_rand j _ (MAX - 1) _ ⊤ (by omega) $$ Hspec with ⟨%m, Hspec, %Hm⟩
      tp_pures j
      wp_pures
      iexists 0
      iframe Hspec
      ipureintro
      rfl
    have hn2 : ¬ n ≤ 1 := by omega
    simp only [hn0, hn2, decide_false]
    tp_pures j
    wp_pures
    wp_alloc l as Hl
    wp_pure
    wp_pure
    wp_pure
    have hn : 0 < n := by omega
    have hnM : n < MAX := by omega
    obtain ⟨h1, h2, h3⟩ := rej_facts MAX n hn hnM
    have e1 : Int.tmod (MAX : ℤ) (n : ℤ) = ((MAX % n : ℕ) : ℤ) := (Int.ofNat_tmod _ _).symm
    have e2 : ((MAX : ℤ) - ((MAX % n : ℕ) : ℤ) - 1) = ((MAX - MAX % n - 1 : ℕ) : ℤ) := by
      omega
    rw [e1, e2]
    generalize (0 : ℤ) = z
    iloeb as IH generalizing %z Hl Hspec
    tp_bind j (Rand _ _)
    wp_pures
    wp_apply wp_couple_fragmented_rand_rand_inj (M := MAX - MAX % n - 1) (N := MAX - 1)
      (rej_f MAX n) (rej_f_inj MAX n) j _ (by omega) (rej_f_dom MAX n hn hnM) $$ Hspec
      with %x ⟨%Hx, H⟩
    simp only [fill_binopl]
    icases H with (⟨%m, %Hm, %Hfm, Hspec⟩ | ⟨%Hcontra, Hspec⟩)
    · -- accepted
      subst Hfm
      obtain ⟨Ha1, Ha2⟩ := rej_f_accept MAX n hn hnM m Hm
      have hlt : ¬ ((rej_f MAX n m : ℕ) : ℤ) < (MAX : ℤ) % (n : ℤ) := by
        rw [← Int.natCast_mod]; exact_mod_cast Nat.not_lt.2 Ha1
      tp_pures j
      wp_store
      wp_load
      wp_pures
      simp only [hlt, decide_false]
      wp_pures
      wp_load
      wp_pures
      simp only [← Int.ofNat_tmod]
      iexists m % n
      iframe Hspec
      rw [Ha2]
      imodintro
      ipureintro
      rfl
    · -- rejected
      have hlt : (x : ℤ) < (MAX : ℤ) % (n : ℤ) := by
        rw [← Int.natCast_mod]; exact_mod_cast rej_f_reject MAX n hn hnM x Hx Hcontra
      wp_store
      wp_load
      wp_pures
      simp only [hlt, _root_.decide_true]
      wp_pure
      iapply IH $$ Hl Hspec

end Foxtrot.Examples.Libsodium
