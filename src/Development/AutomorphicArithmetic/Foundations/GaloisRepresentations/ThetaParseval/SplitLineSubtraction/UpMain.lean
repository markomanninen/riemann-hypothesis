module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PEmbSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.MapUnivAdd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatId
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.UpOfHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PBaseNG
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.LiftSatUHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExHolds

@[expose] public section

namespace UpperTheory.Gal.TP.Sub

theorem upOf : UpOf := upOf_holds embSplit_holds wtId_holds satId_holds UpperTheory.Gal.TP.Loc.liftSatU_holds

theorem baseNG : BaseNG := baseNG_holds UpperTheory.Gal.TP.Skew.skewLine_holds

end UpperTheory.Gal.TP.Sub
