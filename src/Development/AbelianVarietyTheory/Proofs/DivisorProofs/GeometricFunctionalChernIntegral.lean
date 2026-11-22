module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosedStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
public import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
public import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsometryPullIdComp
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDerivChernConnectionInverseSymmetricG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionHeightLowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveDensityExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChartMetricBlockForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtHolomorphicFrameChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormOfGramMatrixAtCompHolomorphic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothFormsCalculusHolomorphicAtlasStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousMemSpanLinearRoots
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPowerHermitianFormDensity

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm.GeoInt

open ReciprocityTheory.L2DbarEstimates (V cHess)
open GlobalTheory.HermFrame (ddc kappa)
open GlobalTheory.GoodMetric (coordVec)

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}

theorem mem_span_pow_lin {ι : Type} [Fintype ι] (d : ℕ) (F : MvPolynomial ι ℝ) (hF : F.IsHomogeneous d) :
    F ∈ Submodule.span ℝ (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d) := by
  by_contra hnot
  obtain ⟨φ, hφF, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hkill : ∀ n : ι → ℤ, φ (lin (fun i => (n i : ℝ)) ^ d) = 0 := by
    intro n
    have hm : lin (fun i => (n i : ℝ)) ^ d ∈ Submodule.span ℝ
        (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d) := Submodule.subset_span ⟨n, rfl⟩
    have h2 : φ (lin (fun i => (n i : ℝ)) ^ d) ∈ (Submodule.span ℝ
        (Set.range fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ d)).map φ := Submodule.mem_map_of_mem hm
    rw [hφ] at h2
    exact (Submodule.mem_bot ℝ).mp h2
  have hP : PowLinSpan.polOf φ d = 0 := by
    refine eq_zero_of_eval_zero_at_prod_finset (PowLinSpan.polOf φ d)
      (fun _ => (Finset.range (d + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_
    · intro x
      rw [Finset.card_image_of_injective _ Nat.cast_injective]
      simpa using Nat.lt_succ_of_le (PowLinSpan.degreeOf_polOf_le φ d x)
    · intro v hv
      have hv' : ∀ i, ∃ k : ℕ, (k : ℝ) = v i := by
        intro i
        obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hv i)
        exact ⟨k, hk⟩
      choose k hk using hv'
      rw [PowLinSpan.eval_polOf]
      have h := hkill (fun i => (k i : ℤ))
      have he : (∑ x, C (v x) * X x : MvPolynomial ι ℝ) = lin (fun i => (((k i : ℤ)) : ℝ)) := by
        simp only [lin, Int.cast_natCast, hk]
      rw [he]
      exact h
  exact hφF (PowLinSpan.homog_kill φ d hP F hF)

section Linear

variable {M : Type} [TopologicalSpace M] {m : ℕ} (A : HolAtlas M m) {ι : Type} (w : ι → A.Pt → Ev m)

theorem evalF_add (G₁ G₂ : MvPolynomial ι ℝ) : evalF A w (G₁ + G₂) = evalF A w G₁ + evalF A w G₂ := by
  funext x
  simp [evalF, fld]

theorem evalF_smul (t : ℝ) (G : MvPolynomial ι ℝ) : evalF A w (t • G) = (t : ℂ) • evalF A w G := by
  funext x
  simp [evalF, fld, Algebra.smul_def]

end Linear

end GlobalTheory.LineForm.GeoInt
