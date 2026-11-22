module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TopOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExpBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExpDisj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EvLemOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.PevExp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DomOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SqExpH
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TopUpOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TorFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.QROf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.ExistsDual
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.WExpH
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.RFinEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNearH
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.AutCrit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.AutMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NrmAut
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOfA
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SumRep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOffHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EmbProjHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NeatLev
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.EllCOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TwistOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TwistBd
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.LadicWeightAtEmbeddingOverPlace
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.KaplFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.KaplOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.SepPoly
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.NearSub
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.Pieces
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamOfOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamExOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.FamSum

@[expose] public section

namespace UpperTheory.Gal.Wt

theorem expBasic_holds : ExpBasic := expBasic_of
theorem expDisj_holds : ExpDisj := expDisj_of
theorem evLem_holds : EvLem := evLem_of
theorem pevExp_holds : PevExp := pevExp_of expBasic_holds
theorem dom_holds : Dom := dom_of
theorem sqExp_holds : SqExp := sqExp_h expBasic_holds evLem_holds dom_holds
theorem topUp_holds : TopUp := topUp_of
theorem torFacts_holds : TorFacts := torFacts_of
theorem qR_holds : QR := qR_of
theorem wtBd_holds : WtBd := wtBd_of expBasic_holds expDisj_holds sqExp_holds topUp_holds torFacts_holds
theorem wExp_holds : WExp := wExp_h expBasic_holds sqExp_holds torFacts_holds
theorem rFinEx_holds : RFinEx := rFinEx_of
theorem deltaNear_holds : DeltaNear := deltaNear_h
theorem autCrit_holds : AutCrit := autCrit_of
theorem autMul_holds : AutMul := autMul_of
theorem nrmAut_holds : NrmAut := nrmAut_of autCrit_holds
theorem famOfA_holds : FamOfA := famOfA_of autMul_holds nrmAut_holds rFinEx_holds
theorem sumRep_holds : SumRep := sumRep_of
theorem neatLev_holds : NeatLev := neatLev_of
theorem ellC_holds : EllC := ellC_of
theorem twist_holds : Twist := twist_of autCrit_holds
theorem twistBd_holds : TwistBd := twistBd_of twist_holds
theorem ladic_weight_embedding_over_place : Kap0 := ladic_weight_at_embedding_over_place
theorem kaplFin_holds : KaplFin := kaplFin_of
theorem kapl_holds : Kapl := kapl_of kaplFin_holds
theorem sepPoly_holds : SepPoly := sepPoly_of kapl_holds
theorem nearSub_holds : NearSub := nearSub_of
theorem pieces_holds : Pieces := pieces_of sepPoly_holds nearSub_holds
theorem famOf_holds : FamOf := famOf_of expBasic_holds pevExp_holds sqExp_holds topUp_holds wExp_holds famOfA_holds
theorem famEx_holds : FamEx := famEx_of neatLev_holds ellC_holds twist_holds twistBd_holds ladic_weight_embedding_over_place pieces_holds deltaNear_holds famOf_holds
theorem famProj_holds : FamProj := famProj_of evLem_holds sumRep_holds
theorem famSum_holds : FamSum := famSum_of expBasic_holds evLem_holds torFacts_holds qR_holds wtBd_holds embProj_holds
theorem famWt_holds : FamWt := famWt_of famOff_holds famSum_holds

theorem wtLacEx_holds : UpperTheory.Gal.Int.Cong.WtLacEx := top_of famEx_holds famProj_holds famWt_holds

end UpperTheory.Gal.Wt
