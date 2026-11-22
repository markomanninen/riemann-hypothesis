module

public import Mathlib
public import Formalism.PeriodIntegrals.AdBridgeSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MaximalCompactConjugacy.Assembly
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeRealK
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK

@[expose] public section

theorem adelic_maximal_compact : ∀ I : Formalism.MainNotions.S.AutInst, Formalism.L2.SG.AdBridge.AdBridgeK I :=
  PI.BridgeMaxCptWork.bridgeMaxCpt_of adelic_compact_real_places adelic_compact_finite_places
