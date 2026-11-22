module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Proposition5Gram
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.OperatorWeightBoundHolds
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.MemRed
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Lemma5aMonomial
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.JointEIntList
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TwistSubXMemSupported
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.Lemma5aGeneratorProducts
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.SymGSupport
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.WordLossNonneg

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.TestSideCounting

theorem stmtE_of_TenMP (hT : TenOp) (D : Formalism.BasicNotions.D7)
    (hM : ∀ CLa Ck Crk Cdeg : ℝ, RestMEM D CLa Ck Crk Cdeg)
    (hP : ∀ CLa Ck Crk Cdeg : ℝ, Proposition5Gram D CLa Ck Crk Cdeg 26 2 24 60) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_TenNS hT D fun CLa Ck Crk Cdeg => restNS_of D CLa Ck Crk Cdeg 26 2 24 60 (hM _ _ _ _) (hP _ _ _ _)

theorem stmtE_of_MP (D : Formalism.BasicNotions.D7)
    (hM : ∀ CLa Ck Crk Cdeg : ℝ, RestMEM D CLa Ck Crk Cdeg)
    (hP : ∀ CLa Ck Crk Cdeg : ℝ, Proposition5Gram D CLa Ck Crk Cdeg 26 2 24 60) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_TenMP tensor_operators_holds D hM hP

end Formalism.MainNotions.TestSideWords
