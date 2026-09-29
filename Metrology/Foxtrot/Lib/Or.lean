module

public import Metrology.Foxtrot.Lib.Nodet

/-!
# Nondeterministic choice

Ported from clutch/theories/foxtrot/lib/or.v

`or e1 e2` runs `e1` or `e2`, depending on the (nondeterministic) result of `nodet #()`.

## Rocq → Lean map
* `or`, `wp_or`, `tp_or`: same names.

## Deviations
* Texan triples are iris-lean's `{{ P }} (e) @ s; ⊤ {{ v, RET v; Q }}` (Rocq: no mask, i.e.
  `⊤`); Rocq's `j ⤇ fill K e -∗ pupd E E (..)` is the entailment `j ⤇ fill K e ⊢ pupd E E (..)`.
* The Rocq `case_bool_decide` on the comparison `#n = #0` is a `by_cases` on `n = 0`.
* `Local Set Default Proof Using "Type*"` has no Lean counterpart.
-/

@[expose] public section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang
open Foxtrot.Lib.Nodet

namespace Foxtrot.Lib.Or

/-- Rocq: `or`. -/
def or (e1 e2 : expr) : expr := cpl(
    if &nodet #() = #0
    then &e1
    else &e2)

section proof

variable {GF : BundledGFunctors} [foxtrotGS GF]
variable {s : Stuckness}

/-- Rocq: `wp_or`. -/
theorem wp_or (e1 e2 : expr) (Φ : val → IProp GF) :
    {{ WP e1 @ s; ⊤ {{ Φ }} ∧ WP e2 @ s; ⊤ {{ Φ }} }} (or e1 e2) @ s; ⊤
    {{ (v : val), RET v; Φ v }} := by
  unfold or
  iintro %ψ H Hψ
  wp_pures
  wp_apply wp_nodet $$ [] with %n -
  · itrivial
  wp_pures
  by_cases hn : n = 0
  · rw [decide_eq_true hn]
    wp_pure
    icases H with ⟨H, -⟩
    iapply wp_wand $$ H Hψ
  · rw [decide_eq_false hn]
    wp_pure
    icases H with ⟨-, H⟩
    iapply wp_wand $$ H Hψ

end proof

section proof'

variable {GF : BundledGFunctors} [foxtrotGS GF]

/-- Rocq: `tp_or`. -/
theorem tp_or (j : ℕ) (K : List ectx_item) (E : CoPset) (b : Bool) (e1 e2 : expr) :
    j ⤇ fill K (or e1 e2) ⊢@{IProp GF}
      pupd E E (if b then iprop(j ⤇ fill K e1) else iprop(j ⤇ fill K e2)) := by
  unfold or
  iintro Hspec
  tp_bind j cpl(&nodet #())
  cases b
  · imod tp_nodet j _ E 1 $$ Hspec with Hspec
    tp_pures j
    simp only [Bool.false_eq_true, ↓reduceIte]
    imodintro
    iexact Hspec
  · imod tp_nodet j _ E 0 $$ Hspec with Hspec
    tp_pures j
    simp only [↓reduceIte]
    imodintro
    iexact Hspec

end proof'

end Foxtrot.Lib.Or
