module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldFiniteAdeleTensorEquivMemIntegralAdeles
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
theorem _root_.GlobalTheory.T.cmFieldFiniteAdeleTensorEquiv_mem_integralAdeles : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E), a ∈ ReciprocityTheory.Aut.ALint D.host.E → GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E := by
  first | exact @GlobalTheory.FixedConj.adeleEquiv_mem_intAf | exact GlobalTheory.FixedConj.adeleEquiv_mem_intAf | (intros; apply GlobalTheory.FixedConj.adeleEquiv_mem_intAf <;> assumption)
