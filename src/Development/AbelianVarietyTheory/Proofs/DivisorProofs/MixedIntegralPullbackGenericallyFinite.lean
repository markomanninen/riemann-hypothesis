module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureMapPullbackGenericallyFiniteStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.PushInt

theorem mixInt_pull : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → (Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) = π.residueDegree (genericPoint Y) * Mix.int L f := by
  intro F _ X Y _ _ p q σ D h1 h2 h3 π hπ hg hk L f hf
  have hm : Measurable (ptMap π hπ σ) := (PtsOver.continuous_map π hπ (spMap σ)).measurable
  have key := fun ε => GlobalTheory.T.mixedChernMeasure_map_pullback_genericallyFinite F X Y p q σ D h1 h2 h3 π hπ hg hk L ε
  have hc0 : ((π.residueDegree (genericPoint Y) : ENNReal)) ≠ 0 := by exact_mod_cast hk
  have hcT : ((π.residueDegree (genericPoint Y) : ENNReal)) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hI : ∀ ε, Integrable (fun y => f (ptMap π hπ σ y)) (part (fun i => (L i).pull π hπ) ε) ↔
      Integrable f (part L ε) := by
    intro ε
    have e := integrable_map_measure (μ := part (fun i => (L i).pull π hπ) ε) hf.aestronglyMeasurable hm.aemeasurable
    rw [key ε, integrable_smul_measure hc0 hcT] at e
    exact e.symm
  have hJ : ∀ ε, ∫ y, f (ptMap π hπ σ y) ∂(part (fun i => (L i).pull π hπ) ε) =
      (π.residueDegree (genericPoint Y) : ℝ) * ∫ y, f y ∂(part L ε) := by
    intro ε
    rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable, key ε, integral_smul_measure]
    simp
  refine ⟨?_, ?_⟩
  · simp only [Intg, hI]
  · simp only [Mix.int, hJ]
    ring

end GlobalTheory.PushInt
