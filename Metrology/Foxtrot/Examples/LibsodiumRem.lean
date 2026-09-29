module

public import Metrology.Foxtrot.Examples.Libsodium

/-!
# `randombytes_uniform`: `rbu_rem ≤ctx≤ rbu_fork`

Ported from clutch/theories/foxtrot/examples/libsodium.v (part 2b: the second `last first`
goal of `randombytes_uniform_refines_ideal`).

The RHS fork is taken with `tp_fork` (Rocq: `pupd_fork`), and the LHS
`rand (MAX - MAX rem n - 1)` is coupled with the two RHS samplings `rand (n - 1)` and
`rand (MAX quot n - 1)` by `wp_couple_rand_two_rands` along `(x, y) ↦ x + y * n`.

## Rocq → Lean map
* `rbu_rem_refines_fork` (Rocq: anonymous subgoal).

## Deviations
* The side conditions of `wp_couple_rand_two_rands` are the lemmas `two_rands_cond1/2/3`,
  and the rewriting of the bounds (Rocq: `Nat2Z.inj_*`, `Z.rem_mod_nonneg`, `Z.quot_div_nonneg`)
  are the equations `e1`, `e2`, `e3` (using `max_sub_rem`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE COFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.BinaryRel

namespace Foxtrot.Examples.Libsodium

theorem rbu_rem_refines_fork (MAX : ℕ) :
    (∅ : varmap type) ⊨ Val (rbu_rem MAX) ≤ctx≤ Val (rbu_fork MAX) : TArrow TNat TNat := by
  apply start
  intro _ n K j
  iintro Hspec
  unfold rbu_rem rbu_fork
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
      tp_fork j as j' Hspec'
      tp_pures j
      tp_pures j'
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
      wp_bind (Rand _ _)
      wp_apply wp_couple_rand_two_rands (n - 1) (MAX / n - 1) (fun x y => x + y * n) K []
        _ _ _ j j' (Int.toNat_natCast _).symm (Int.toNat_natCast _).symm rfl (two_rands_cond1 n _ hn0 hq) (two_rands_cond2 n _ hn0)
        (two_rands_cond3 n _ hn0 hq) $$ [Hspec Hspec'] with %x ⟨%a, %b, %Ha, %Hb, %Hx, Hspec, -⟩
      · iframe Hspec
        rw [fill_nil']
        iexact Hspec'
      wp_pures
      iexists a
      iframe Hspec
      ipureintro
      subst Hx
      rw [← Int.ofNat_tmod, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

end Foxtrot.Examples.Libsodium
