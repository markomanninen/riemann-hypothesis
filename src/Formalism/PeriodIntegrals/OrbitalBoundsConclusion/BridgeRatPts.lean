module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalPointsComparison.BridgeApplyEqOfComp

@[expose] public section

theorem adelic_rational_points : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeGF I :=
  Formalism.L2.SG.AdBridge.adBridgeGF_main
