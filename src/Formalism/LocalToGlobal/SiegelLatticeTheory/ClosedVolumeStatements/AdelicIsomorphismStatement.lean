module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.AdBridge
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Mathlib
public import Formalism.PeriodIntegrals.AdBridgeSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.ContinuousOfHAInf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.LinearIndependentOneBeta
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.CoordFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.LatticeOfEntriesIntegral
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeMaxCpt
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeRatPts

@[expose] public section

namespace Formalism.L2.SG.Closed

theorem AdBridgeIso_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeIso I :=
  Formalism.L2.SG.Pf.adelic_isomorphism_exists (I := I)

theorem AdBridgeGF_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeGF I := adelic_rational_points I

theorem AdBridgeK_holds (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdBridgeK I := adelic_maximal_compact I

theorem adelic_isomorphism_statement (I : Formalism.MainNotions.S.AutInst) : Formalism.L2.SG.AdBridge.AdelicIsomorphism I :=
  Formalism.L2.SG.Pf.adelic_isomorphism_of_parts (I := I) (adelic_rational_points I) (adelic_maximal_compact I)

end Formalism.L2.SG.Closed
