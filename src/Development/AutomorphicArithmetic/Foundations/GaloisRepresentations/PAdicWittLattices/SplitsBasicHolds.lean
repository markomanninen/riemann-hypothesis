module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PExtPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClosD
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClos
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMultiSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeFun
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeInj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PExtTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PExtGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtInj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTrBase
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTrPushM
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesAbs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopSpec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesGen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesOp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PCoverInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPieceLe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwGal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPlInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopDeep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFnRing
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopLin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopOp

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct

universe u v

namespace UpperTheory.Gal.G3

theorem isoPts_holds : IsoPts := @pIsoPts

theorem ptsOfSplits_holds : PtsOfSplits := @pPtsOfSplits

theorem splitsPts_holds : SplitsPts := pSplitsPts isoPts_holds

theorem extPts_holds : ExtPts := @pExtPts

theorem fEtBasic_holds : FEtBasic := pFEtBasic ptsOfSplits_holds

theorem splitsBasic_holds : SplitsBasic := pSplitsBasic splitsPts_holds ptsOfSplits_holds

theorem splitsComp_holds : SplitsComp := pSplitsComp splitsPts_holds ptsOfSplits_holds

theorem bcSplits_holds : BcSplits := @pBcSplits @splitsBasic_holds

theorem bcGal_holds : BcGal := pBcGal bcSplits_holds

theorem ordStep_holds : OrdStep := @pOrdStep

theorem ordEx_holds : OrdEx := pOrdEx ordStep_holds

theorem galClosD_holds : GalClosD := pGalClosD splitsPts_holds ordEx_holds

theorem galClos_holds : GalClos := pGalClos galClosD_holds

theorem multiSplit_holds : MultiSplit := pMultiSplit fEtBasic_holds splitsBasic_holds galClosD_holds

theorem algIsoPts_holds : AlgIsoPts := pAlgIsoPts isoPts_holds

theorem algSplit_holds : AlgSplit := @pAlgSplit @algIsoPts_holds

theorem algTr_holds : AlgTr := @pAlgTr

theorem hodgeFun_holds : ∀ (k : Type) [Field k] {Z Y W : Scheme.{0}} (p : Z ⟶ sp k) (q : Y ⟶ sp k) (r : W ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c), Splits s c σ → ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)), GlobalTheory.HodgeCoh.appSec p r c U (secTrace p q hU b) = ∑ j, GlobalTheory.CechDR.Sec.res r (GlobalTheory.GalTrace.preimage_le (hσ j) U) (GlobalTheory.HodgeCoh.appSec q r (σ j) (s ⁻¹ᵁ U) b) := pHodgeFun ptsOfSplits_holds algSplit_holds algTr_holds

theorem hodgeTr_holds : HodgeTr := @pHodgeTr @hodgeFun_holds

theorem hodgeInj_holds : HodgeInj := @pHodgeInj

theorem hodgeGood_holds : HodgeGood := @pHodgeGood @hodgeTr_holds @hodgeInj_holds

theorem etTr_holds : EtTr := @pEtTr

theorem etnGood_holds : EtnGood := @pEtnGood @fEtBasic_holds @etTr_holds

theorem etGood_holds : EtGood := @pEtGood @etnGood_holds

theorem bcGood_holds : BcGood.{u} := pBcGood bcSplits_holds bcGal_holds

theorem extTr_holds : ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L) :=
  @pExtTr.{u}

theorem extGood_holds : ExtGood.{u} := pExtGood extTr_holds

theorem opTr_holds : OpTr.{u} := @pOpTr.{u}

theorem opEx_holds : OpEx.{u} := pOpEx opTr_holds

theorem galInv_holds : GalInv.{u} := @pGalInv.{u}

theorem opEt_holds : OpEt := @pOpEt

theorem opBc_holds : OpBc.{u} := pOpBc bcSplits_holds bcGal_holds

theorem fEtInj_holds : FEtInj.{u} := pFEtInj galClosD_holds

theorem trBase_holds : TrBase.{u} := pTrBase fEtBasic_holds splitsBasic_holds galClosD_holds

theorem trPushM_holds : TrPushM.{u} := pTrPushM fEtBasic_holds splitsBasic_holds splitsComp_holds multiSplit_holds fEtInj_holds

theorem liesAbs_holds : LiesAbs.{u} := pLiesAbs fEtBasic_holds trBase_holds trPushM_holds

theorem hopSpec_holds : HopSpec := pHopSpec etGood_holds bcGood_holds galClos_holds opEx_holds opTr_holds opEt_holds opBc_holds bcSplits_holds

theorem liesGen_holds : LiesGen := @pLiesGen

theorem liesOp_holds : LiesOp.{u} := pLiesOp liesGen_holds liesAbs_holds

theorem coverInv_holds : CoverInv.{u} := pCoverInv galInv_holds splitsPts_holds

theorem pieceLe_holds : PieceLe := pPieceLe etGood_holds bcGood_holds extGood_holds extTr_holds hopSpec_holds coverInv_holds

theorem twSplit_holds : TwSplit := pTwSplit splitsPts_holds

theorem twGal_holds : TwGal := pTwGal twSplit_holds

end UpperTheory.Gal.G3
