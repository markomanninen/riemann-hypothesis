module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PushAFinsumInter
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2DbarChartMeasureTransfer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeComplexPointsProperClosedChartFieldStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernNullField

theorem chernPart_compl_null : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → ∀ U : X.Opens, genericPoint X ∈ U → ∀ (B : LB X) (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε (ptsIn p σ U)ᶜ = 0 := by
  intro k _ X _ p σ D _ U hU B φ ε
  have hcX : (ptsIn p σ U)ᶜ =
      {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((U : X.Opens) : Set X)ᶜ} := by
    ext y
    simp [mem_ptsIn]
  have hA : MeasurableSet (ptsIn p σ U)ᶜ := (isOpen_ptsIn U).measurableSet.compl
  have glue_null {n : ℕ} {Y ι : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
      (e : ι → OpenPartialHomeomorph Y (ReciprocityTheory.L2DbarEstimates.V n))
      (ρ : ι → Y → ENNReal) {F : Set Y} (hF : MeasurableSet F)
      (h0 : ∀ i, volume ((e i) '' ((e i).source ∩ F)) = 0) :
      GlobalTheory.ChartGlue.glueMeas e ρ F = 0 := by
    have hc : ∀ i, GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) F = 0 := fun i => by
      rw [GlobalTheory.ChartGlue.chartMeas_apply (e i) (ρ i) hF]
      exact setLIntegral_measure_zero _ _ (h0 i)
    have hle : GlobalTheory.ChartGlue.glueMeas e ρ ≤ (GlobalTheory.ChartGlue.glueMeas e ρ).restrict Fᶜ := by
      refine iSup_le fun i => Measure.le_iff.2 fun B hB => ?_
      rw [Measure.restrict_apply hB]
      calc GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) B ≤ GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) (B ∩ Fᶜ ∪ F) :=
            measure_mono fun y hy => by
              by_cases h : y ∈ F
              · exact Or.inr h
              · exact Or.inl ⟨hy, h⟩
        _ ≤ GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) (B ∩ Fᶜ) + GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) F := measure_union_le _ _
        _ = GlobalTheory.ChartGlue.chartMeas (e i) (ρ i) (B ∩ Fᶜ) := by rw [hc i, add_zero]
        _ ≤ GlobalTheory.ChartGlue.glueMeas e ρ (B ∩ Fᶜ) :=
            Measure.le_iff'.1 (le_iSup (fun i => GlobalTheory.ChartGlue.chartMeas (e i) (ρ i)) i) _
    have h := Measure.le_iff'.1 hle F
    rw [Measure.restrict_apply hF, inter_compl_self, measure_empty] at h
    exact nonpos_iff_eq_zero.1 h
  refine glue_null _ _ hA fun c => ?_
  rw [hcX]
  exact GlobalTheory.T.volume_complexPoints_properClosed_chart_field k X p σ D _ U.isOpen.isClosed_compl (by simpa using hU) c

end GlobalTheory.ChernNullField

end
