module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EllipticOnePole
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiProductOfThetaWeber

@[expose] public section

namespace GlobalTheory.ThetaWeberObj

theorem thetaWeberStatement : GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeberStatement :=
  GlobalTheory.ThetaWeberRoad.thetaWeberStatement_of Formalism.L2.Th1.F.thetaLine Formalism.L2.Th1.F.sgStarBasic
    Formalism.L2.Th1.F.sgStarAdd

end GlobalTheory.ThetaWeberObj
