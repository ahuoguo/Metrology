module

public import Metrology.Foxtrot.SpecProofMode
public import Metrology.Foxtrot.CouplingRulesMisc

/-!
# Biased coin tosses

Ported from clutch/theories/foxtrot/lib/toss.v

`toss p q e1 e2` runs `e1` with probability `p / (q + 1)` and `e2` otherwise.
`wp_toss_simplify` couples `toss (k * p) ((q + 1) * k - 1) e1 e2` (on the left) with
`toss p q e3 e4` (on the right), for `k > 0`: both tosses have the same bias.

## Rocq → Lean map
* `toss`, `wp_toss_simplify`: same names.

## Deviations
* Rocq's `k > 0 → y = .. → x = .. → □ .. -∗ □ .. -∗ {{{ P }}} e @ E {{{ v, RET v; Φ v }}}` is
  `k > 0 → y = .. → x = .. → ⊢ □ .. -∗ □ .. -∗ {{ P }} (e) @ s; E {{ v, RET v; Φ v }}`
  (inside an `iprop`, iris-lean's Texan triple is `□ ∀ Φ, P -∗ ▷ (..) -∗ WP e {{ Φ }}`, as in
  Rocq). The hypotheses are named `Hk`, `Hy`, `Hx`.
* The Rocq `case_bool_decide` on the comparison is a `by_cases`; the arithmetic side conditions
  (Rocq: `Nat.Div0.div_lt_upper_bound`, `Nat.div_le_lower_bound`) are `Nat.div_lt_iff_lt_mul`.
* `Local Set Default Proof Using "Type*"` has no Lean counterpart.
-/

@[expose] public section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.Lib.Toss

/-- Rocq: `toss`. The bias here is `p / (q + 1)`. -/
def toss (p q : ℕ) (e1 e2 : expr) : expr := cpl(
    if rand(#q) < #p
    then &e1
    else &e2)

section proof

variable {GF : BundledGFunctors} [foxtrotGS GF]
variable {s : Stuckness}

/-- Rocq: `wp_toss_simplify`. -/
theorem wp_toss_simplify (p q k x y : ℕ) (e1 e2 e3 e4 : expr) (j : ℕ) (K : List ectx_item)
    (E : CoPset) (Φ : val → IProp GF) (Hk : k > 0) (Hy : y = (q + 1) * k - 1) (Hx : x = k * p) :
    ⊢ □ (j ⤇ fill K e3 -∗ WP e1 @ s; E {{ Φ }}) -∗
      □ (j ⤇ fill K e4 -∗ WP e2 @ s; E {{ Φ }}) -∗
      {{ j ⤇ fill K (toss p q e3 e4) }} (toss x y e1 e2) @ s; E {{ v, RET v; Φ v }} := by
  subst Hy Hx
  iintro #H1 #H2 !> %ψ Hspec Hψ
  unfold toss
  tp_bind j (Rand _ _)
  wp_apply (wp_couple_toss (x := (q + 1) * k - 1) (y := q) (k := k) j _ Hk rfl) $$ Hspec
    with %n Hspec
  wp_pures
  tp_pures j
  by_cases H0 : (n : ℤ) < (k : ℤ) * (p : ℤ)
  · have Hdiv : (n : ℤ) / (k : ℤ) < (p : ℤ) := by
      have : n < p * k := by
        rw [Nat.mul_comm]
        exact_mod_cast H0
      exact_mod_cast (Nat.div_lt_iff_lt_mul Hk).2 this
    rw [decide_eq_true H0]
    rw [decide_eq_true Hdiv]
    tp_pures j
    wp_pures
    iapply wp_wand $$ [Hspec] Hψ
    iapply H1 $$ Hspec
  · have Hdiv : ¬ (n : ℤ) / (k : ℤ) < (p : ℤ) := by
      have : ¬ n < p * k := by
        rw [Nat.mul_comm]
        exact_mod_cast H0
      intro h
      exact this ((Nat.div_lt_iff_lt_mul Hk).1 (by exact_mod_cast h))
    rw [decide_eq_false H0]
    rw [decide_eq_false Hdiv]
    tp_pures j
    wp_pures
    iapply wp_wand $$ [Hspec] Hψ
    iapply H2 $$ Hspec

end proof

end Foxtrot.Lib.Toss
