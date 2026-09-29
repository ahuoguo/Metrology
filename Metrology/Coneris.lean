module

public import Metrology.Coneris.Weakestpre
public import Metrology.Coneris.Lifting
public import Metrology.Coneris.EctxLifting
public import Metrology.Coneris.PrimitiveLaws
public import Metrology.Coneris.DerivedLaws
public import Metrology.Coneris.WpTactics
public import Metrology.Coneris.ProofMode
public import Metrology.Coneris.WpUpdate
public import Metrology.Coneris.ErrorRules
public import Metrology.Coneris.Atomic
public import Metrology.Coneris.Adequacy

@[expose] public section

/-!
# Coneris

Coneris, a concurrent probabilistic separation logic with error credits, for `con_prob_lang`.
Ported from `clutch/theories/coneris` (and `clutch/theories/con_prob_lang/wp_tactics.v`): the
weakest precondition and its lifting lemmas, primitive and derived laws, the proof-mode
tactics, the `wp_update`/`state_update` modalities, error-credit rules, logically atomic
triples, and adequacy.
-/
