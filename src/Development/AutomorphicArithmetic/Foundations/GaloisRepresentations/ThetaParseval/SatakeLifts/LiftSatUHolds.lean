module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.IsUnitaryCharInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.LeftSmooth
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.KeepsSB
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.ModelDict
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.Separates
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLift
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SrcGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.ContraIrr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.ContraUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatContra
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatTwist
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatInvT
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatDet
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatProd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SegInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnitPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PullGoodPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairSatPf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.LiftSatUPf

@[expose] public section

namespace UpperTheory.Gal.TP.Loc

theorem liftIso_holds : LiftIso :=
  liftIso_of (pairOfLift leftSmooth keepsSB modelDict separates) srcGood contraIrr (contraUnit contraIrr)

theorem liftSat_holds : LiftSat :=
  liftSat_of liftIso_holds srcGood contraIrr (contraUnit contraIrr) (satContra (contraUnit contraIrr)) satTwist satInvT satDet
    satProd segInv

theorem pairSat_holds : PairSat :=
  pairSat liftSat_holds pullGood contraIrr (contraUnit contraIrr) (satContra (contraUnit contraIrr))

theorem liftSatU_holds : LiftSatU := liftSatU pairSat_holds compUnit

end UpperTheory.Gal.TP.Loc
