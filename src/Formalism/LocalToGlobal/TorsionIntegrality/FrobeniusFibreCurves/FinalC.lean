module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementC
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.BaseChangeCompatible
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NormHalfB2SubTwoTorsionLeOne

@[expose] public section

namespace Formalism.L2.Th1.B

theorem baseChange : BaseChange := Map.baseChangeCompatible
theorem curveSigma : CurveSigma := Crv.curve_sigma_function_holds
theorem weierstrass_biadditive_mod_equiv : WeierstrassBiadditiveModEquiv := Crv.curve_formal_first_level_holds

end Formalism.L2.Th1.B
