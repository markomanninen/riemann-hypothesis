module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaZeroTranslateProduct
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassPSecondDerivative

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.F

namespace SemicharacterPairingLemmas

open OperatorUThetaLemmas

end SemicharacterPairingLemmas

open SemicharacterPairingLemmas OperatorUThetaLemmas

theorem operator_u_theta : OpUTh0 := by
  intro L t x z
  rw [← opUMul L x t (sgStar L) z]
  simp only [th0, opU]
  ring

end Formalism.L2.Th1.F
