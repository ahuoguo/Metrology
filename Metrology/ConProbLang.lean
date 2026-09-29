module

public import Metrology.ConProbLang.Common.Locations
public import Metrology.ConProbLang.Common.ConLanguage
public import Metrology.ConProbLang.Common.ConEctxLanguage
public import Metrology.ConProbLang.Common.ConEctxiLanguage
public import Metrology.ConProbLang.Common.SchErasable
public import Metrology.ConProbLang.Lang
public import Metrology.ConProbLang.Notation
public import Metrology.ConProbLang.Common.ConInject
public import Metrology.ConProbLang.Tactics
public import Metrology.ConProbLang.Metatheory
public import Metrology.ConProbLang.CtxSubst
public import Metrology.ConProbLang.ClassInstances
public import Metrology.ConProbLang.SolveRedIris
public import Metrology.ConProbLang.Erasure
public import Metrology.ConProbLang.LubTermination
public import Metrology.ConProbLang.Spec.SpecRA
public import Metrology.ConProbLang.Spec.SpecTactics
public import Metrology.ConProbLang.Typing.Types
public import Metrology.ConProbLang.Typing.ContextualRefinement
public import Metrology.ConProbLang.Typing.Tychk

@[expose] public section

/-!
# ConProbLang

The concurrent probabilistic language `con_prob_lang` (heap_lang without prophecies, plus tapes
and random sampling) with `Distr`-valued head/prim steps and a scheduler (MDP) thread-pool
semantics, together with the generic concurrent language interfaces from `clutch/theories/common`.
Ported from `clutch/theories/con_prob_lang` and `clutch/theories/common`; the language of the
Coneris and Foxtrot ports.
-/
