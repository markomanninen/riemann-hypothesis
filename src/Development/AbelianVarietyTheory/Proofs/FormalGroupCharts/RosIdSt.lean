module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ActStOf
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsGoodConst
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeIndependenceAll
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TopLePreimageWchart
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.EvalStandardPointsThree
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RelatedMap
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AddOfPtPt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ToJetOneEqSum
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RepJetAugCompTrunc
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RosatiCubicalAdditive
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RosatiGenOneMulStar
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExUniqueSer
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsNilpotentOfMemKerJetTruncR
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.TwoChartAddOfPtPt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ValSerGermFnVal
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap

@[expose] public section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB GlobalTheory.JetSer

namespace GlobalTheory.JetRoad

theorem rosIdSt : RosIdSt := by
  intro S G _ _ h2 h3 Lr c O _ _ act u hu T z J hJ
  have a := GlobalTheory.RosatiCube.rosati_cubical_additive S G h2 h3 Lr c O act u hu T z J hJ
  have b := GlobalTheory.rosatiGen_one_mul_star S G h2 h3 Lr c O act u hu T z J hJ
  exact ⟨a.1, a.2.1, b.1, b.2.1, a.2.2, b.2.2⟩

theorem jetRoad : JetAlgSt ∧ RepSt ∧ LawSt ∧ MapSt ∧ DLinSt ∧ ActSt ∧ TwoChartSt ∧ SerSt ∧
    SerExSt ∧ FBOfSt ∧ HMulSt ∧ GermExSt ∧ IntTransSt ∧ ChartBCSt := by
  have hJ : JetAlgSt := jetAlg
  have hR : RepSt := repSt_of_jetAlgSt hJ
  have hL : LawSt := lawSt_of hJ hR
  have hM : MapSt := (GlobalTheory.JetMap.mapSt_and_dLinSt hJ hR).1
  have hD : DLinSt := (GlobalTheory.JetMap.mapSt_and_dLinSt hJ hR).2
  have hA : ActSt := GlobalTheory.ChartAction.actSt_of hJ hR hM
  have hT : TwoChartSt := twoChart_of_rep_map hJ hR hM
  have hS : SerSt := serSt_of_jetAlgSt hJ
  have hE : SerExSt := serEx hJ hR hS
  exact ⟨hJ, hR, hL, hM, hD, hA, hT, hS, hE,
    FBOf.fbOf hJ hR hL hM hA hS hE valSer rosIdSt,
    FrameChange.hMul hJ hR hT hS hE,
    GlobalTheory.GermExist.germ_exists_unique hJ hR hS hE,
    IntTrans.intTrans GlobalTheory.canonGauge_independence_all.2.2.2 GlobalTheory.exists_formalBiext_map,
    GlobalTheory.ChartBaseChange.chartBaseChange hJ hS⟩

end GlobalTheory.JetRoad
