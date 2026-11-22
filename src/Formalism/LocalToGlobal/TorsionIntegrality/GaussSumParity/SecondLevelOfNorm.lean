module

public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.NonVac
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLevelOfNormHolds

@[expose] public section

namespace Formalism.L2.Th1.D

theorem chainNonVacuous : ChainNonVacuous := chain_nonvacuous
theorem normUnits : NormUnits := norm_units_alt

end Formalism.L2.Th1.D
