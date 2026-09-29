module

public import Metrology.Foxtrot.SpecProofMode

/-!
# A diverging function

Ported from clutch/theories/foxtrot/lib/diverge.v

## Rocq → Lean map
* `diverge`, `wp_diverge`: same names.

## Deviations
* Rocq's `{{{ True }}} diverge #() {{{ v, RET v; False }}}` (at mask `⊤`) is iris-lean's Texan
  triple `{{ True }} (diverge #()) @ s; ⊤ {{ v, RET v; False }}`.
* `Local Set Default Proof Using "Type*"` has no Lean counterpart.
-/

@[expose] public section

open Iris Iris.BI Iris.Std Iris.ProofMode OFE ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.Lib.Diverge

/-- Rocq: `diverge`. -/
def diverge : val := cpl_val(
  rec f _ :=
    f #())

section proof

variable {GF : BundledGFunctors} [foxtrotGS GF]
variable {s : Stuckness}

/-- Rocq: `wp_diverge`. -/
theorem wp_diverge :
    {{ True }} (cpl(&diverge #())) @ s; ⊤ {{ v, RET v; (False : IProp GF) }} := by
  iintro %Φ - -
  unfold diverge
  iloeb as IH
  wp_pure
  iexact IH

end proof

end Foxtrot.Lib.Diverge
