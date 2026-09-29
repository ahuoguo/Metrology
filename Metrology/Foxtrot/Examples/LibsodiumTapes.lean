module

public import Metrology.Foxtrot.Examples.Libsodium

/-!
# `randombytes_uniform`: the tape steps of `ideal_refines_randombytes_uniform`

Ported from clutch/theories/foxtrot/examples/libsodium.v (part 2d: the first three
`ctx_refines_transitive` goals of `ideal_refines_randombytes_uniform`).

## Rocq → Lean map
* `ideal_refines_tapes`: `ideal_uniform ≤ctx≤ rbu_tapes` (`wp_couple_rand_rand_lbl`).
* `tapes_refines_rem`: `rbu_tapes ≤ctx≤ rbu_rem` (`pupd_couple_two_tapes_rand`, then
  `wp_randtape`).
* `rem_refines_rem_tape`: `rbu_rem ≤ctx≤ rbu_rem_tape` (`wp_couple_rand_rand_lbl`).

## Deviations
* As in the other parts, bijections found by instance search in Rocq (`id`) are explicit,
  and the rewritings of the bounds are the equations `e1`, `e2`, `e3`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.BinaryRel

namespace Foxtrot.Examples.Libsodium

theorem ideal_refines_tapes (MAX : ℕ) :
    (∅ : varmap type) ⊨ Val (ideal_uniform MAX) ≤ctx≤ Val (rbu_tapes MAX) :
      TArrow TNat TNat := by
  apply start
  intro _ n K j
  iintro Hspec
  unfold ideal_uniform rbu_tapes
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
    by_cases hn : n = 0
    · simp only [hn, decide_true]
      tp_pures j
      wp_pures
      iexists 0
      iframe Hspec
      ipureintro
      rfl
    · simp only [hn, decide_false]
      tp_pures j
      wp_pures
      tp_allocnattape j α as Hα
      tp_pures j
      tp_allocnattape j β as Hβ
      tp_pures j
      wp_apply wp_couple_rand_rand_lbl _ id Function.bijective_id _ K α j rfl (fun _ h => h) $$
        [Hα Hspec] with %m ⟨-, Hspec, -⟩
      · iframe Hα Hspec
      simp only [id]
      iexists m
      iframe Hspec
      ipureintro
      rfl

end Foxtrot.Examples.Libsodium

namespace Foxtrot.Examples.Libsodium

theorem tapes_refines_rem (MAX : ℕ) :
    (∅ : varmap type) ⊨ Val (rbu_tapes MAX) ≤ctx≤ Val (rbu_rem MAX) :
      TArrow TNat TNat := by
  apply start
  intro _ n K j
  iintro Hspec
  unfold rbu_tapes rbu_rem
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
    by_cases hn : n = 0
    · simp only [hn, decide_true]
      tp_pures j
      wp_pures
      iexists 0
      iframe Hspec
      ipureintro
      rfl
    · simp only [hn, decide_false]
      tp_pures j
      wp_pures
      wp_alloctape α as Hα
      wp_pures
      wp_alloctape β as Hβ
      wp_pures
      have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      have hq : 0 < MAX / n := Nat.div_pos (by omega) hn0
      have e1 : ((n : ℤ) - 1) = ((n - 1 : ℕ) : ℤ) := by omega
      have e2 : ((MAX : ℤ) / (n : ℤ) - 1) = ((MAX / n - 1 : ℕ) : ℤ) := by
        rw [← Int.natCast_div]; omega
      have e3 : ((MAX : ℤ) - Int.tmod (MAX : ℤ) (n : ℤ) - 1) =
          (((n - 1 + 1) * (MAX / n - 1 + 1) - 1 : ℕ) : ℤ) := by
        rw [max_sub_rem, Nat.sub_add_cancel hn0, Nat.sub_add_cancel hq]
        have : 0 < n * (MAX / n) := Nat.mul_pos hn0 hq
        omega
      rw [e1, e2, e3]
      simp only [Int.toNat_natCast]
      tp_bind j (Rand _ _)
      imod pupd_couple_two_tapes_rand (n - 1) (MAX / n - 1) (fun x y => x + y * n) _ ⊤ α β
        _ _ _ [] [] j (Int.toNat_natCast _).symm (Int.toNat_natCast _).symm rfl
        (two_rands_cond1 n _ hn0 hq) (two_rands_cond2 n _ hn0) (two_rands_cond3 n _ hn0 hq)
        $$ Hα Hβ Hspec with ⟨%a, %b, Hα, -, Hspec, %Ha, %Hb⟩
      simp only [fill_binopl]
      tp_pures j
      have hmod : Int.tmod ((a : ℤ) + (b : ℤ) * (n : ℤ)) (n : ℤ) = (a : ℤ) := by
        rw [show ((a : ℤ) + b * n) = ((a + b * n : ℕ) : ℤ) by push_cast; ring,
          ← Int.ofNat_tmod, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      rw [hmod, List.nil_append]
      wp_randtape as Hα
      iexists a
      iframe Hspec
      ipureintro
      rfl

end Foxtrot.Examples.Libsodium

namespace Foxtrot.Examples.Libsodium

theorem rem_refines_rem_tape (MAX : ℕ) :
    (∅ : varmap type) ⊨ Val (rbu_rem MAX) ≤ctx≤ Val (rbu_rem_tape MAX) :
      TArrow TNat TNat := by
  apply start
  intro _ n K j
  iintro Hspec
  unfold rbu_rem rbu_rem_tape
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
    by_cases hn : n = 0
    · simp only [hn, decide_true]
      tp_pures j
      wp_pures
      iexists 0
      iframe Hspec
      ipureintro
      rfl
    · simp only [hn, decide_false]
      tp_pures j
      wp_pures
      tp_allocnattape j α as Hα
      tp_pures j
      tp_bind j (Rand _ _)
      wp_bind (Rand _ _)
      wp_apply wp_couple_rand_rand_lbl _ id Function.bijective_id _ _ α j rfl (fun _ h => h) $$
        [Hα Hspec] with %m ⟨-, Hspec, -⟩
      · iframe Hα Hspec
      simp only [id, fill_binopl]
      tp_pures j
      wp_pures
      simp only [← Int.ofNat_tmod]
      iexists m % n
      iframe Hspec
      ipureintro
      rfl

end Foxtrot.Examples.Libsodium
