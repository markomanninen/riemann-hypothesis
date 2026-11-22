module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SPowSmooth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsProjOverSPow
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PtsOfSplits
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemiHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PFnDecomp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHopWord
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGeoStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PAltLin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeEig
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.POccOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PKSHodge
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PMapEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PModelBc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHomEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPolPull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTatePull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTransPull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PLegBc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPowComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.LevelIsPullback
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PKNNormal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCntFn
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCntSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSigmaFEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSigmaSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PullCongr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PKSProj

@[expose] public section

namespace UpperTheory.Gal.LocalSmoothExtension

theorem HopWord_holds : HopWord := hopWord_of Tw.fnRing Tw.hopLin Tw.hopMul
theorem TransPull_holds : TransPull := transPull_of homEx_of polPull_of tatePull_of
theorem KSBc_holds : KSBc := kSBc_of (modelBc_of mapEq_of) (legBc_of mapEq_of TransPull_holds) powComp_of
theorem MemOp_holds : MemOp :=
  memOp2_of kNNormal_of cntFn_of cntSum_of sigmaFEt_of (sigmaSplit_of sigmaFEt_of Tw.splitsPts Tw.ptsOfSplits)
    Tw.twGal Tw.hopEx
theorem OccOf_holds : OccOf :=
  occOf_of MemOp_holds Tw.hodgeGood Tw.hodgeTr Tw.bcGood Tw.opBc Tw.opTr Tw.bcSplits
theorem KSProj_holds : KSProj := kSProj_of GlobalTheory.WeightTwoHeckePower.sPow_smooth GlobalTheory.WeightTwoHeckePower.isProjOver_sPow

theorem hodgeTrace_of_lefschetz_and_groupSide : HodgeTraceFromLefschetzAndGroupSide := fun hW hP hF h₁ h₂ =>
  have hT : UpperTheory.Gal.LocalSmoothExtension.HodgeTr :=
    hodgeTr_of (GroupTop_of h₁ h₂) fnDecomp_of HopWord_holds altLin_of
      (geoStep_of hW hP hF lefSum_of Tw.hodgeGood Tw.hodgeTr Tw.hopOp Tw.opTr)
      CxLin_holds Tw.hodgeGood
  have hE : HodgeEig :=
    hodgeEig_of hT hP (hodgeFin_of hW) unifBound_of hExpInj_of coeffOcc_of EigOf_holds HopWord_holds Tw.hodgeGood
  ⟨hT, hE, kSHodge_of hE KSBc_holds SpecConj_holds MemOp_holds fnDecomp_of OccOf_holds⟩

theorem ksHodge_of_inputs (hW : HolomorphicLefschetzFormula) (hF : FixK) (h₁ : GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd) (h₂ : GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace) :
    UpperTheory.Gal.Int.Geo.KSHodge :=
  (hodgeTrace_of_lefschetz_and_groupSide hW KSProj_holds hF h₁ h₂).2.2

end UpperTheory.Gal.LocalSmoothExtension
