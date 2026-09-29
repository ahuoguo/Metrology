module

public import Metrology.Foxtrot.Adequacy
public import Metrology.Foxtrot.BinaryRel.BinaryModel

/-!
# Adequacy of Foxtrot's binary logical relation

Ported from clutch/theories/foxtrot/binary_rel/binary_adequacy_rel.v

A refinement `↯ ε ⊢ REL e << e' : A` whose relation `A` implies a pure `ϕ` yields an
approximate coupling between the executions of `e` and `e'` (`foxtrot_rel_adequacy`), and
hence a bound on the least upper bounds of their termination probabilities
(`foxtrot_rel_adequacy'`).

## Rocq → Lean map
* `foxtrotRGpreS` (constructor `FoxtrotRGPreS`, field `foxtrotRGpreS_foxtrot`, an instance),
  `foxtrot_rel_adequacy`, `foxtrot_rel_adequacy'`: same names (namespace `Foxtrot.BinaryRel`).

## Deviations
* Errors are `ℝ≥0∞` (Rocq: `R`): the hypotheses `0 <= ε` are dropped, `ε' > 0` is `0 < ε'`, and
  Rocq's `Rbar_le a (Rbar_plus b ε)` is `a ≤ b + ε` (as in `Metrology.Foxtrot.Adequacy`).
* The ghost-functor bundle `GF` is explicit (Rocq: `Σ`); `∀ `{foxtrotRGS Σ}, ..` is
  `∀ [foxtrotRGS GF], ..`, and `A : ∀ `{foxtrotRGS Σ}, lrel Σ` is `A : ∀ [foxtrotRGS GF], lrel GF`.
* The scheduler state is a `Type` with `[DecidableEq] [Countable]` (Rocq: `Countable`), and
  `∃ `(Countable sch_int_σ') sch' ζ' `(!TapeOblivious ..)` is spelled out as in
  `foxtrot_adequacy_intermediate`.
* The hypothesis `∀ v v', A v v' -∗ ⌜ϕ v v'⌝` is `∀ v v', A v v' ⊢ ⌜ϕ v v'⌝`.

## Omitted
* `foxtrotRΣ` and `subG_foxtrotRGPreS`: iris-lean has no `gFunctors` lists / `subG` (as for
  `foxtrotΣ` in `Metrology.Foxtrot.PrimitiveLaws`).
-/

@[expose] public section

noncomputable section

open scoped ENNReal
open Iris Iris.BI Iris.Std Iris.ProofMode OFE Prob ConProbLang ConProbLang.con_prob_lang

namespace Foxtrot.BinaryRel

/-- Rocq: `foxtrotRGpreS`. -/
class foxtrotRGpreS (GF : BundledGFunctors) where
  FoxtrotRGPreS ::
  foxtrotRGpreS_foxtrot : foxtrotGpreS GF

attribute [reducible, instance] foxtrotRGpreS.foxtrotRGpreS_foxtrot

set_option quotPrecheck false in
/-- The state type of `con_lang_mdp con_prob_lang` (reducibly `cfg`). -/
local notation "CPState" => (con_lang_mdp con_prob_lang).mdpstate

/-- Rocq: `foxtrot_rel_adequacy`. The hypothesis `0 <= ε` is dropped. -/
theorem foxtrot_rel_adequacy (GF : BundledGFunctors) [foxtrotRGpreS GF]
    (A : ∀ [foxtrotRGS GF], lrel GF) (ϕ : val → val → Prop) (e e' : expr) (σ σ' : state)
    (ε : ℝ≥0∞)
    (HA : ∀ [foxtrotRGS GF], ∀ v v', A v v' ⊢ ⌜ϕ v v'⌝)
    (Hlog : ∀ [foxtrotRGS GF], ↯ ε ⊢ REL e << e' : A) :
    ∀ (sch_int_σ : Type) [DecidableEq sch_int_σ] [Countable sch_int_σ]
      (sch : scheduler (con_lang_mdp con_prob_lang) sch_int_σ) (ζ : sch_int_σ)
      [TapeOblivious sch_int_σ sch] (ε' : ℝ≥0∞) (n : ℕ), 0 < ε' →
      ∃ (sch_int_σ' : Type) (_ : DecidableEq sch_int_σ') (_ : Countable sch_int_σ')
        (sch' : scheduler (con_lang_mdp con_prob_lang) sch_int_σ') (ζ' : sch_int_σ')
        (_ : TapeOblivious sch_int_σ' sch'),
        ARcoupl (sch_exec sch n (ζ, ([e], σ))) (sch_lim_exec sch' (ζ', (([e'], σ') : CPState)))
          ϕ (ε + ε') := by
  intro sch_int_σ _ _ sch ζ _ ε' n Hε'
  refine foxtrot_adequacy_intermediate GF ε ϕ n e e' ?_ sch_int_σ sch ζ σ σ' ε' Hε'
  intro H'
  let HfoxtrotR : foxtrotRGS GF := foxtrotRGS.FoxtrotRGS H'
  iintro Herr Hspec
  ihave Hlog := @Hlog HfoxtrotR $$ Herr
  -- `refines_eq`/`refines_def`, and `fill [] e' = e'` (Rocq: `fill_empty`)
  unfold refines refines_def
  ihave Hspec := (show 0 ⤇ e' ⊢@{IProp GF} 0 ⤇ fill [] e' from .rfl) $$ Hspec
  ihave Hlog := Hlog $$ %([] : List ectx_item) %0 Hspec
  iapply wp_mono (fun v => ?_) $$ Hlog
  iintro ⟨%v', Hj, Hv⟩
  iexists v'
  isplitl [Hj]
  · iapply (show 0 ⤇ fill [] (Val v') ⊢@{IProp GF} 0 ⤇ Val v' from .rfl) $$ Hj
  iapply (@HA HfoxtrotR v v') $$ Hv

/-- Rocq: `foxtrot_rel_adequacy'`. The hypothesis `0 <= ε` is dropped; Rocq's
`Rbar_le a (Rbar_plus b ε)` is `a ≤ b + ε` in `ℝ≥0∞`. -/
theorem foxtrot_rel_adequacy' (GF : BundledGFunctors) [foxtrotRGpreS GF]
    (A : ∀ [foxtrotRGS GF], lrel GF) (ϕ : val → val → Prop) (e e' : expr) (σ σ' : state)
    (ε : ℝ≥0∞)
    (HA : ∀ [foxtrotRGS GF], ∀ v v', A v v' ⊢ ⌜ϕ v v'⌝)
    (Hlog : ∀ [foxtrotRGS GF], ↯ ε ⊢ REL e << e' : A) :
    lub_termination_prob e σ ≤ lub_termination_prob e' σ' + ε :=
  ARcoupl_lub e e' σ σ' ε ϕ fun n sch_int_σ _ _ sch ζ _ ε' Hε' =>
    foxtrot_rel_adequacy GF A ϕ e e' σ σ' ε HA Hlog sch_int_σ sch ζ ε' n Hε'

end Foxtrot.BinaryRel
