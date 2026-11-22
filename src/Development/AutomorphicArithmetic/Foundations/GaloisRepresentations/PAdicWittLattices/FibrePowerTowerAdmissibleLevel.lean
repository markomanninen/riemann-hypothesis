module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PNuInt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMultBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKNBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSysOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAdmOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKNCong
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGSimOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRelComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTateDiff
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTateTwist
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFullOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRelArith
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransSelf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHomPull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTatePull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransPull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransOfMap
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRigid
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsogFEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransKer
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PQuotUniq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPolUniq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMapOfIso
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransUniqPt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDeep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransIso
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransOrbit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransFree
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGenSm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPowSm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.GObjMapCast
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtOrbit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitUniq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitCart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitForget
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitDeep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PDescMap
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHomDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPolDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransCancel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitTrans
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitFree
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwFEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSigmaFEt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSumFn
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMemOp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKSNice
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.ExistsDeeperNormalLevel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasicHolds

@[expose] public section

open UpperTheory.Gal.Int.Geo (KSEx KSNice)

universe u

namespace UpperTheory.Gal.G3

theorem nuInt_holds : NuInt := @pNuInt

theorem multBasic_holds : MultBasic := @pMultBasic @nuInt_holds

theorem kNBasic_holds : KNBasic := @pKNBasic

theorem sysOf_holds : SysOf := @pSysOf @nuInt_holds

theorem fibrePowerTower_admissibleLevel : AdmOf := @pAdmOf

theorem kNCong_holds : KNCong := @pKNCong

theorem gSimOf_holds : GSimOf := @pGSimOf @multBasic_holds

theorem relComp_holds : RelComp := @pRelComp

theorem tateDiff_holds : TateDiff := @pTateDiff

theorem tateTwist_holds : TateTwist := @pTateTwist @gSimOf_holds

theorem fullOf_holds : FullOf := @pFullOf

theorem relArith_holds : RelArith := @pRelArith

theorem transSelf_holds : TransSelf := @pTransSelf @multBasic_holds @relComp_holds @tateTwist_holds

theorem transComp_holds : TransComp := @pTransComp @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds

theorem homPull_holds : HomPull := @pHomPull

theorem tatePull_holds : TatePull := @pTatePull

theorem transPull_holds : TransPull := @pTransPull @homPull_holds @tatePull_holds

theorem transOfMap_holds : TransOfMap := @pTransOfMap @multBasic_holds @relComp_holds @tatePull_holds

theorem rigid_holds : Rigid := @pRigid

theorem isogFEt_holds : IsogFEt := @pIsogFEt

theorem transKer_holds : TransKer := @pTransKer @relComp_holds @tateDiff_holds @tateTwist_holds

theorem polUniq_holds : PolUniq := @pPolUniq

theorem mapOfIso_holds : MapOfIso := @pMapOfIso

theorem transDeep_holds : TransDeep := @pTransDeep @sysOf_holds @fibrePowerTower_admissibleLevel @fullOf_holds @relArith_holds

theorem transIso_holds : TransIso := @pTransIso @isoPts_holds @isogFEt_holds

theorem transOrbit_holds : TransOrbit := @pTransOrbit @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @kNCong_holds @transIso_holds

theorem transFree_holds : TransFree := @pTransFree @kNCong_holds

theorem genSm_holds : GenSm := @pGenSm

theorem powSm_holds : PowSm := @pPowSm @genSm_holds

theorem etDesc_holds : EtDesc := @pEtDesc @extPts_holds

theorem ptOrbit_holds : PtOrbit := @pPtOrbit @transComp_holds @transPull_holds @transOfMap_holds @transOrbit_holds @rigid_holds

theorem witComp_holds : WitComp := @pWitComp @transSelf_holds @transComp_holds @transPull_holds

theorem witCart_holds : WitCart := @pWitCart @transIso_holds

theorem witForget_holds : WitForget := @pWitForget @mapOfIso_holds @transSelf_holds

theorem witDeep_holds : WitDeep := @pWitDeep @kNBasic_holds @genSm_holds @transDeep_holds @witComp_holds @witForget_holds

theorem homDesc_holds : HomDesc := @pHomDesc @etDesc_holds

theorem polDesc_holds : PolDesc := @pPolDesc

theorem transDesc_holds : TransDesc := @pTransDesc @isogFEt_holds @tatePull_holds @homDesc_holds @polDesc_holds

theorem transCancel_holds : TransCancel := @pTransCancel @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @transIso_holds

theorem twFEt_holds : TwFEt := @pTwFEt @fEtBasic_holds @twGal_holds

theorem sigmaFEt_holds : SigmaFEt := @pSigmaFEt

theorem kSNice_holds : KSNice := @pKSNice @kNBasic_holds @powSm_holds @twFEt_holds @sigmaFEt_holds

theorem quotUniq_holds : QuotUniq := @pQuotUniq @etDesc_holds

theorem transUniqPt_holds : TransUniqPt := @pTransUniqPt @multBasic_holds @isogFEt_holds @transKer_holds @quotUniq_holds @polUniq_holds @mapOfIso_holds

theorem ptEq_holds : PtEq := @pPtEq @transSelf_holds @transComp_holds @transPull_holds @transUniqPt_holds @rigid_holds

theorem witUniq_holds : WitUniq := @pWitUniq @genSm_holds @extPts_holds @transSelf_holds @ptEq_holds

theorem descMap_holds : DescMap := @pDescMap @genSm_holds @etDesc_holds @ptEq_holds @ptOrbit_holds @witCart_holds

theorem witEx_holds : WitEx := @pWitEx @kNBasic_holds @genSm_holds @rigid_holds @witForget_holds @witDeep_holds @descMap_holds @transIso_holds @transCancel_holds @transDesc_holds

theorem witOne_holds : WitOne := @pWitOne @genSm_holds @witUniq_holds @witComp_holds @witForget_holds

theorem witTrans_holds : WitTrans := @pWitTrans @kNBasic_holds @ptEq_holds @ptOrbit_holds @witComp_holds

theorem witFree_holds : WitFree := @pWitFree @kNBasic_holds @transComp_holds @transPull_holds @transOfMap_holds @transFree_holds @ptEq_holds @witCart_holds @witEx_holds

theorem kSEx_holds : KSEx := @pKSEx @kNBasic_holds @witUniq_holds @witComp_holds @witCart_holds @witEx_holds @witOne_holds @witTrans_holds @witFree_holds

end UpperTheory.Gal.G3
