module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceBaseNeOfDistinctTypePrimes
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSpec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WBEqPrimeComap
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommTensCastRSymmMap
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_base_ne_of_distinct_type_primes : ∀ (D : D7) (s s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (kv kv' : Σ k : Fin 2, D.nd.PlG k), s.w = D.naut.plGw kv.1 kv.2 → s'.w = D.naut.plGw kv'.1 kv'.2 → kv ≠ kv' → s.v ≠ s'.v := by
  first | exact @GlobalTheory.SplitPlaceDistinct.splitPlace_v_ne | exact GlobalTheory.SplitPlaceDistinct.splitPlace_v_ne | (intros; apply GlobalTheory.SplitPlaceDistinct.splitPlace_v_ne <;> assumption)
