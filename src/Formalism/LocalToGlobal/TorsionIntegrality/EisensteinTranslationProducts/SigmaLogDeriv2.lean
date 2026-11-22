module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.AnalyticIdentityTheoremsZetaFacts
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaConv
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaBasic
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaLog
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ZetaQuasi
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaQuasi
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.EtaEis
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Legendre

@[expose] public section

namespace Formalism.L2.Th1.F

theorem zetaSummable : ZetaSummable := zeta_summable
theorem zetaHasDeriv : ZetaHasDeriv := zeta_has_deriv
theorem zetaOdd : ZetaOdd := zeta_odd
theorem zetaQuasi : ZetaQuasi := zetaQuasi_of zetaHasDeriv zetaOdd
theorem sigmaSummable : SigmaSummable := sigma_summable
theorem sigmaProdLU : SigmaProdLU := sigma_product_locally_uniform
theorem sigmaEntire : SigmaEntire := sigmaEntire_of sigmaProdLU
theorem sigmaOdd : SigmaOdd := sigma_odd
theorem sigmaZero : SigmaZero := sigmaZero_of sigmaSummable
theorem sigmaLogDeriv : SigmaLogDeriv := sigmaLogDeriv_of sigmaProdLU sigmaSummable zetaSummable
theorem sigmaQuasi : SigmaQuasi := sigmaQuasi_of zetaQuasi sigmaLogDeriv sigmaEntire sigmaOdd sigmaZero
theorem sigmaSimple : SigmaSimple := sigmaSimple_of sigmaQuasi sigmaEntire (sigmaDerivZero_of sigmaProdLU)
theorem etaEisenstein : EtaEisenstein := etaEisenstein_of zetaSummable zetaOdd
theorem legendre : Legendre := legendre_of etaEisenstein

end Formalism.L2.Th1.F
