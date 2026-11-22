module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocFour
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PHenselV
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSplitRep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PBlockMat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadMap
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PScale
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadicUnitNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PPadicSqFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PTrivMat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PCongrScale
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PSplitCongr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PInfCongr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PDefSign
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PRelOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PLocRoot
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PZUnitNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PZSqFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PAdFour
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PUnitCls
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PFinCongr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PNormTwo
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PFinCls
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.PIsoEx

@[expose] public section

namespace UpperTheory.Gal.G1

theorem LocFour_holds : LocFour := pLocFour
theorem HenselV_holds : HenselV := pHenselV
theorem SplitRep_holds : SplitRep := pSplitRep
theorem BlockMat_holds : BlockMat := pBlockMat
theorem PadMap_holds : PadMap := pPadMap
theorem Scale_holds : Scale := pScale
theorem PadicUnitNorm_holds : PadicUnitNorm := pPadicUnitNorm
theorem PadicSqFin_holds : PadicSqFin := pPadicSqFin
theorem TrivMat_holds : TrivMat := pTrivMat
theorem CongrScale_holds : CongrScale := pCongrScale
theorem SplitCongr_holds : SplitCongr := pSplitCongr
theorem InfCongr_holds : InfCongr := pInfCongr
theorem DefSign_holds : DefSign := pDefSign
theorem RelOf_holds : RelOf := pRelOf
theorem LocUnit_holds : LocUnit := pLocUnit HenselV_holds
theorem LocRoot_holds : LocRoot := pLocRoot HenselV_holds
theorem ZUnitNorm_holds : ZUnitNorm := pZUnitNorm PadicUnitNorm_holds
theorem ZSqFin_holds : ZSqFin := pZSqFin PadicSqFin_holds
theorem AdFour_holds : AdFour := pAdFour LocFour_holds LocUnit_holds LocRoot_holds SplitRep_holds
theorem UnitCls_holds : UnitCls := pUnitCls Scale_holds ZUnitNorm_holds ZSqFin_holds
theorem FinCongr_holds : FinCongr := pFinCongr PadMap_holds LocRoot_holds TrivMat_holds CongrScale_holds SplitCongr_holds DefSign_holds
theorem NormTwo_holds : NormTwo := pNormTwo AdFour_holds
theorem FinCls_holds : FinCls := pFinCls UnitCls_holds FinCongr_holds InfCongr_holds DefSign_holds RelOf_holds
theorem IsoEx_holds : IsoEx := pIsoEx NormTwo_holds BlockMat_holds

end UpperTheory.Gal.G1
