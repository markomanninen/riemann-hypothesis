module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxPosDens
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimple
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartZeroSet
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartDim
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PGoodChartModel
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeVanishingHomog
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PConeSliceIdeal
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PChartDehomogPrime
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PComponentsGenericCount
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSheetLift
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsGenericCount
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetSimpleNull
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CxSimpleOfCount

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open MeasureTheory CxInt CxComp

theorem cxSheetSimpleNull : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Q : Ideal (MRingOver ℂ ι)) (e : ℕ) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsCxVar Q e → IsSetGoodProj (conePts Q) Ψ →
    volume {y : Fin e → ℂ | ∃ w ∈ setFibre (conePts Q) Ψ y, (∃ γ, IsSetSheet (conePts Q) Ψ y w γ) ∧
      ¬ cxSimple (conePts Q) Ψ w} = 0 := by
  intro K _ ι _ Q e Ψ hQ hΨ
  obtain ⟨d, hbd, hnull⟩ := cxGenericCount hQ Ψ hΨ
  refine measure_mono_null (fun y hy => ?_) hnull
  obtain ⟨w, hw, -, hns⟩ := hy
  exact fun hgood => hns (cxSimple_of_count hbd hgood.1 hgood.2 hw)

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
