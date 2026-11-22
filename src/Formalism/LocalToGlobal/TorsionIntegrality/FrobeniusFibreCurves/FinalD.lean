module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalC
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.XTwoDvdOfRestrictThirdZero
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Wp3ApplyEqSqMulSubSqMul
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.RealAdelicInertTransportTypeFormsEqAlt
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffLawWithInverseThree
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.FirstLevelOfThreeVarParallelogram
public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LawDifferenceThree

@[expose] public section

namespace Formalism.L2.Th1.B

open Formalism.L2.Th1.A (bridgeWp bridgeLaw bridgeCurve bridgeCurve3)

theorem shearLemma : ShearLemma := Wr.shearedWronskianUniqueness
theorem tauRule : TauRule := Det.tau_derivative_rule_holds
theorem detRule : DetRule := Det.determinant_derivative_rule_holds
theorem frobStickLog : FrobStickLog := Fs.FrobStickLog_of shearLemma tauRule detRule
theorem frobStick : FrobStick := Fs.FrobStick_of frobStickLog
theorem frobStickStar : FrobStickStar := Fs.FrobStickStar_of frobStick
theorem fIUnit : FIUnit := E2.formal_inverse_unit_holds
theorem parThree : ParThree := E2.ParThree_of frobStickStar fIUnit
theorem cubeFromPars : CubeFromPars := E3.cube_relation_from_parallelograms
theorem first_level_all_formal_groups : LogSigmaPullbackCocycleJets := E3.log_sigma_pullback_cocycle_jets_of_parallelogram_and_cube parThree cubeFromPars

end Formalism.L2.Th1.B
