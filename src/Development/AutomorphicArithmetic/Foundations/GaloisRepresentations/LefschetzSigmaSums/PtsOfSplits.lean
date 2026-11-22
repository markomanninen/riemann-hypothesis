module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwGal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPlInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopDeep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFnRing
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopLin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopOp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeFun
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeInj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeGood

@[expose] public section

namespace UpperTheory.Gal.LocalSmoothExtension.Tw

open UpperTheory.Gal.G3

theorem splitsPts : SplitsPts := pSplitsPts pIsoPts
theorem ptsOfSplits : PtsOfSplits := pPtsOfSplits
theorem bcSplits : BcSplits := by
  exact pBcSplits (pSplitsBasic splitsPts ptsOfSplits)
theorem bcGood : BcGood.{0} := pBcGood bcSplits (pBcGal bcSplits)
theorem opBc : OpBc.{0} := pOpBc bcSplits (pBcGal bcSplits)
theorem opTr : OpTr.{0} := pOpTr
theorem twSplit : TwSplit := pTwSplit splitsPts
theorem twGal : TwGal := pTwGal twSplit
theorem plInv : PlInv.{0} := pPlInv pGalInv twGal
theorem hopDeep : HopDeep.{0} := pHopDeep plInv
theorem hopEx : HopEx.{0} := pHopEx plInv hopDeep
theorem fnRing : FnRing := pFnRing
theorem hopLin : HopLin.{0} := by
  exact pHopLin fnRing hopDeep hopEx
theorem hopMul : HopMul.{0} := by
  exact pHopMul fnRing hopDeep hopEx
theorem hopOp : HopOp.{0} := by
  exact pHopOp fnRing hopEx twSplit twGal
theorem hodgeTr : HodgeTr := by
  exact pHodgeTr (pHodgeFun ptsOfSplits (pAlgSplit (pAlgIsoPts pIsoPts)) pAlgTr)
theorem hodgeGood : HodgeGood := pHodgeGood hodgeTr pHodgeInj

end UpperTheory.Gal.LocalSmoothExtension.Tw
