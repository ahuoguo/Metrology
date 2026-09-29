module

public import Metrology.Foxtrot.SpecProofMode

/-!
# The minimum of two integers

Ported from clutch/theories/foxtrot/lib/min.v

## Rocq → Lean map
* `min_prog`, `wp_min_prog`, `spec_min_prog`: same names. `x `min` y` is `min x y`.

## Deviations
* Texan triples are iris-lean's `{{ P }} (e) @ s; E {{ (z : ℤ), RET v; Q }}`; Rocq's
  `j ⤇ fill K e -∗ pupd E E (..)` is the entailment `j ⤇ fill K e ⊢ pupd E E (..)`.
* Rocq's `case_bool_decide` is a `by_cases` on `x < y`, rewriting the `decide (x < y)` left
  by the comparison.
-/

@[expose] public section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.Lib.Min

/-- Rocq: `min_prog`. -/
def min_prog : val := cpl_val(
  λ x y,
    if x < y then x else y)

section specs

variable {GF : BundledGFunctors} [foxtrotGS GF]
variable {s : Stuckness}

/-- Rocq: `wp_min_prog`. -/
theorem wp_min_prog (x y : ℤ) (E : CoPset) :
    {{ True }} (cpl(&min_prog #x #y)) @ s; E
    {{ (z : ℤ), RET LitV (LitInt z); (⌜z = min x y⌝ : IProp GF) }} := by
  iintro %Φ - HΦ
  unfold min_prog
  wp_pures
  by_cases h : x < y
  · rw [decide_eq_true h]
    wp_pures
    iapply HΦ $$ []
    ipureintro
    rw [min_eq_left (le_of_lt h)]
  · rw [decide_eq_false h]
    wp_pures
    iapply HΦ $$ []
    ipureintro
    rw [min_eq_right (not_lt.1 h)]

/-- Rocq: `spec_min_prog`. -/
theorem spec_min_prog (E : CoPset) (j : ℕ) (K : List ectx_item) (x y : ℤ) :
    j ⤇ fill K cpl(&min_prog #x #y) ⊢@{IProp GF}
      pupd E E (j ⤇ fill K (Val (LitV (LitInt (min x y))))) := by
  unfold min_prog
  iintro HK
  tp_pures j
  by_cases h : x < y
  · rw [decide_eq_true h]
    tp_pures j
    rw [min_eq_left (le_of_lt h)]
    imodintro
    iexact HK
  · rw [decide_eq_false h]
    tp_pures j
    rw [min_eq_right (not_lt.1 h)]
    imodintro
    iexact HK

end specs

end Foxtrot.Lib.Min
