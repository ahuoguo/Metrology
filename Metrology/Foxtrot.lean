module

public import Metrology.Foxtrot.Oscheduler
public import Metrology.Foxtrot.FullInfo
public import Metrology.Foxtrot.Weakestpre
public import Metrology.Foxtrot.Pupd
public import Metrology.Foxtrot.Lifting
public import Metrology.Foxtrot.EctxLifting
public import Metrology.Foxtrot.PrimitiveLaws
public import Metrology.Foxtrot.DerivedLaws
public import Metrology.Foxtrot.ProofMode
public import Metrology.Foxtrot.ErrorRules
public import Metrology.Foxtrot.CouplingRules
public import Metrology.Foxtrot.CouplingRulesMisc
public import Metrology.Foxtrot.CouplingRulesVonNeumann
public import Metrology.Foxtrot.Adequacy
public import Metrology.Foxtrot.AdequacyInstance
public import Metrology.Foxtrot.ConerisRelate
public import Metrology.Foxtrot.SpecProofMode
public import Metrology.Foxtrot.UnaryRel.UnaryModel
public import Metrology.Foxtrot.UnaryRel.UnaryInterp
public import Metrology.Foxtrot.UnaryRel.UnaryAppRelRules
public import Metrology.Foxtrot.UnaryRel.UnaryRelTactics
public import Metrology.Foxtrot.UnaryRel.UnaryCompatibility
public import Metrology.Foxtrot.UnaryRel.UnaryFundamental
public import Metrology.Foxtrot.BinaryRel.BinaryModel
public import Metrology.Foxtrot.BinaryRel.BinaryInterp
public import Metrology.Foxtrot.BinaryRel.BinaryAppRelRules
public import Metrology.Foxtrot.BinaryRel.BinaryRelTactics
public import Metrology.Foxtrot.BinaryRel.BinaryCompatibility
public import Metrology.Foxtrot.BinaryRel.BinaryFundamental
public import Metrology.Foxtrot.BinaryRel.BinaryFundamentalPart2
public import Metrology.Foxtrot.BinaryRel.BinaryFundamentalPart3
public import Metrology.Foxtrot.BinaryRel.BinaryFundamentalPart4
public import Metrology.Foxtrot.BinaryRel.BinaryFundamentalPart5
public import Metrology.Foxtrot.BinaryRel.BinaryAdequacyRel
public import Metrology.Foxtrot.BinaryRel.BinarySoundness

@[expose] public section

/-!
# Foxtrot

A concurrent probabilistic relational separation logic with error credits, based on oblivious
(full-information) schedulers. Ported from `clutch/theories/foxtrot`.
-/
