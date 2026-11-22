module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.HopExS
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.PieceInS
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.MatInS
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NiceBc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.BcCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.IntMap
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.NegVan
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.GoodOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.SubAdm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.GrCrys
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.CrysStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CorrUniqHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLocTower

@[expose] public section

namespace UpperTheory.Gal.Seam

theorem hopEx_holds : HopEx := hopExS trivial

theorem locTower_holds : LocTower := G3.locTower_of G3.vBcS_holds hopEx_holds niceBc

theorem pieceIn_holds : PieceIn := pieceInS G3.vInv_holds hopEx_holds

theorem matIn_holds : MatIn := matInS G3.vFin_holds pieceIn_holds negVan

theorem crysStep_of (h : CrystallineSemistableComparison.SmoothModelCrystalline) : UpperTheory.Gal.Int.Geo.CrysStep :=
  crysStep h niceBc locTower_holds bcCover intMap goodOf matIn_holds subAdm grCrys

end UpperTheory.Gal.Seam
