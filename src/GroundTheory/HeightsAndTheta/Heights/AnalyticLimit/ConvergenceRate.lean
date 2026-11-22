module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory Filter Topology Set
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt MIntegrable ChartPartition integralWith
  locDens chartPartMeasure integral_chartPartMeasure isFiniteMeasure_chartPartMeasure existsPartition
  locDensCont mIntegrableCont)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell errE)

noncomputable section

theorem tendsto_ell : Tendsto ell (𝓝[>] 0) atTop :=
  Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero

section Signed

variable {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

def tvMeasure (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) : Measure X :=
  ∑ j, (chartPartMeasure A (existsPartition A).some Φ 1 j +
    chartPartMeasure A (existsPartition A).some Φ (-1) j)

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem chart_weight_continuousOn (A : FinHolAtlas D X) (P : ChartPartition A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) :
    ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target := by
  have h := (P.smooth j j).continuousOn
  rw [Set.preimage_univ, Set.inter_univ] at h
  exact continuousOn_const.mul (h.mul (locDensCont A Φ hΦ j))


omit [CompactSpace X] [T2Space X] in
theorem integrableOn_chart_of_part (A : FinHolAtlas D X) (P : ChartPartition A)
    (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) (g : X → ℝ)
    (hg : Measurable g) (hi : Integrable g (chartPartMeasure A P Φ s j)) :
    IntegrableOn (fun y => g ((A.chart j).symm y) *
      max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0) (A.chart j).target := by
  have hT : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  have hwc := chart_weight_continuousOn A P Φ hΦ s j
  have hsymm : AEMeasurable (A.chart j).symm (volume.restrict (A.chart j).target) :=
    (A.chart j).continuousOn_symm.aemeasurable hT
  have hd : AEMeasurable (fun y => ENNReal.ofReal
      (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) (volume.restrict (A.chart j).target) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hwc.aemeasurable hT)
  have hlt : ∀ᵐ y ∂(volume.restrict (A.chart j).target), ENNReal.ofReal
      (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hsymm' : AEMeasurable (A.chart j).symm ((volume.restrict (A.chart j).target).withDensity
      fun y => ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hfun : (fun y => (ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) *
      locDens A Φ j y))).toReal • (g ∘ (A.chart j).symm) y) = fun y => g ((A.chart j).symm y) *
        max (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y)) 0 := by
    funext y
    rw [ENNReal.toReal_ofReal', smul_eq_mul, Function.comp_apply, mul_comm]
  unfold chartPartMeasure at hi
  rw [integrable_map_measure hg.aestronglyMeasurable hsymm',
    integrable_withDensity_iff_integrable_smul₀' hd hlt, hfun] at hi
  exact hi

theorem abs_mInt_le (A : FinHolAtlas D X) (Φ : Fin D → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i))
    (f : X → ℝ) (hf : Measurable f) (hfi : MIntegrable A Φ f) :
    Integrable f (tvMeasure A Φ) ∧ |mInt A Φ f| ≤ ∫ x, |f x| ∂tvMeasure A Φ := by
  have h1 := fun j => integral_chartPartMeasure A (existsPartition A).some Φ hΦ 1 j f hf hfi
  have h2 := fun j => integral_chartPartMeasure A (existsPartition A).some Φ hΦ (-1) j f hf hfi
  have hI : ∀ j, Integrable f (chartPartMeasure A (existsPartition A).some Φ 1 j +
      chartPartMeasure A (existsPartition A).some Φ (-1) j) :=
    fun j => (h1 j).1.add_measure (h2 j).1
  have hm : mInt A Φ f = ∑ j, (∫ x, f x ∂chartPartMeasure A (existsPartition A).some Φ 1 j -
      ∫ x, f x ∂chartPartMeasure A (existsPartition A).some Φ (-1) j) := by
    rw [mInt, dite_eq_left (existsPartition A)]
    unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(h1 j).2, (h2 j).2, ← integral_sub
      (integrableOn_chart_of_part A _ Φ hΦ 1 j f hf (h1 j).1)
      (integrableOn_chart_of_part A _ Φ hΦ (-1) j f hf (h2 j).1)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    dsimp only
    rw [one_mul, neg_one_mul, ← mul_sub, max_zero_sub_max_neg_zero_eq_self]
    ring
  refine ⟨integrable_finsetSum_measure.2 fun j _ => hI j, ?_⟩
  rw [hm, tvMeasure, integral_finsetSum_measure fun j _ => (hI j).abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [integral_add_measure (h1 j).1.abs (h2 j).1.abs]
  exact (abs_sub _ _).trans (add_le_add abs_integral_le_integral_abs abs_integral_le_integral_abs)

end Signed

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential)

@[instance_reducible] def projectiveLineBorel : MeasurableSpace (OnePoint ℂ) := borel _

attribute [local instance] projectiveLineBorel

theorem projectiveLine_borelSpace : BorelSpace (OnePoint ℂ) := ⟨rfl⟩

attribute [local instance] projectiveLine_borelSpace

end Inhabitants

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
