module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Elliptic
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.OnePole
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaOrder
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaAdd
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.PDeriv
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ThreeTermNumEqTwistedGammaOfSigmaZero

@[expose] public section

namespace Formalism.L2.Th1.F

theorem ellipticEntire : EllipticEntire := elliptic_entire_const
theorem ellipticNoPole : EllipticNoPole := elliptic_no_pole_const
theorem ellipticOnePole : EllipticOnePole :=
  ellipticOnePole_of ellipticNoPole ellipticEntire zetaQuasi legendre
theorem sigmaOrder : SigmaOrder := sigmaOrder_of sigmaEntire sigmaZero sigmaSimple
theorem sigmaAdd : SigmaAdd :=
  sigmaAdd_of ellipticNoPole sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaQuasi sigmaOrder
theorem sgStarAdd : SgStarAdd := sgStarAdd_of sigmaAdd
theorem pInjective : PInjective := pInjective_of sigmaAdd sigmaZero
theorem sigmaDouble : SigmaDouble := sigmaDouble_of sigmaAdd sigmaEntire sigmaSimple
theorem pDerivZero : PDerivZero := pDerivZero_of sigmaDouble sigmaZero
theorem discNeZero : DiscNeZero := discNeZero_of pDerivZero pInjective
theorem zetaAdd : ZetaAdd := zetaAdd_of sigmaAdd sigmaLogDeriv sigmaZero
theorem sigmaThree : SigmaThree :=
  sigmaThree_of ellipticOnePole sigmaOrder sigmaQuasi sigmaZero sigmaEntire sigmaOdd sigmaSimple sigmaAdd
theorem sgStarThree : SgStarThree := sgStarThree_of sigmaThree
theorem thetaLine : ThetaLine := thetaLine_of ellipticOnePole sgStarQuasi sgStarBasic

end Formalism.L2.Th1.F
