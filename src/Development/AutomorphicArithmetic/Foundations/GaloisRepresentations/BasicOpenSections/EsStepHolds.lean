module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PGalEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PHopOp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EtOfRestrict
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PLiesOp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PFixDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PTowES
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PPlaceData
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PGrPass
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PEsStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EsGenAll

@[expose] public section

namespace UpperTheory.Gal.Mod

theorem hopOp_holds : HopOp := hopOp @galEx @corrOpEq

theorem towES_holds : TowES := towES esGen_all bcEx (liesOp hopOp_holds @opCover) (fixDesc hopOp_holds)

theorem esStep_holds : UpperTheory.Gal.Int.Geo.ESStep := esStep towES_holds placeData grPass

end UpperTheory.Gal.Mod
