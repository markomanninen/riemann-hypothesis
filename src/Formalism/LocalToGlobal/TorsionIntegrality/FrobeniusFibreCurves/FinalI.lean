module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalE
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BiextensionFormalMulMul
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LinearCoeffLogShiftedWeierstrass
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.PhENormOf
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoAdicScalarConditions
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoTorsionCurveToSeries

@[expose] public section

namespace Formalism.L2.Th1.B

theorem th0Isogeny : Th0Isogeny := Iso.theta_zero_isogeny_holds
theorem phENorm : PhENorm := Nrm.PhENorm_of th0Isogeny
theorem th0Vanish : ThetaZeroVanishing := Van.Th0Vanish_of cubeE phENorm
theorem twoAdicScalars : TwoAdicScalars := Van.two_adic_scalar_conditions

end Formalism.L2.Th1.B
