module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.IwasawaUnitaryAdelic.IUAIwa
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviModulusOneLinearReductiveExpMulExpStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDense
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.StatementB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIsoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLowKOfLeLowKSub
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.PolarJmConjTranspose
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffKAverageRight
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.SArith
public import Formalism.FormalDegreeBessel.StatementDS
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SesqEqZeroOfDiagEqZero
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Formalism.RealPlaceAnalysis.FinalF
public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.SchurOrthogonalityIndefiniteUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentity
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.TraceConjMulEqHilbertSchmidt
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
public import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
public import Formalism.RealPlaceAnalysis.Complexify
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
public import GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntIrrPerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGroupStructuresPermConjInvariant
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsGlobalCharDetPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd

@[expose] public section

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.admitted

theorem isAdmissible_of_unitary_irreducible : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)}, GlobalTheory.LinRed.IsLinRed G →
    PositivityTheory.Tls2.Iua.AdmG G → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsURepOn G σ → Formalism.MainNotions.S.IsIrredOn G σ →
    GlobalTheory.LinRed.IsAdmOn G σ := by
  intro n G hG hA H _ _ _ σ hσ hirr
  refine ⟨hσ.1, hσ.2.2, fun k hk v => hσ.2.1 k hk.1 v, ?_⟩
  intro S hfd hS _
  haveI := hfd
  let b := Module.finBasis ℂ S
  choose Y hYfd _ hvY hY using fun i => hA H σ hσ hirr S hS (b i) (b i).2
  haveI : ∀ i, FiniteDimensional ℂ (Y i) := hYfd
  have hsup : FiniteDimensional ℂ (⨆ i, Y i : Submodule ℂ H) := Submodule.finiteDimensional_iSup Y
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ i, Y i) (sSup_le ?_)
  rintro _ ⟨Θ, rfl, hΘ⟩
  let T : H →L[ℂ] H := (LinearMap.toContinuousLinearMap (Θ.domRestrict S)).comp S.orthogonalProjectionOnto
  have hT : ∀ k ∈ GlobalTheory.LinRed.maxCpt G, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    have hk1 : k * k.conjTranspose = 1 := Matrix.mem_unitaryGroup_iff.1 hk.2
    have hks : k.conjTranspose ∈ GlobalTheory.LinRed.maxCpt G := ⟨hG.star_mem k hk.1, Unitary.star_mem hk.2⟩
    have hiso : ∀ x y, ⟪σ k x, σ k y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y =>
      (LinearIsometry.mk (σ k : H →ₗ[ℂ] H) (hσ.2.1 k hk.1)).inner_map_map x y
    have hP : ((S.orthogonalProjectionOnto (σ k u) : S) : H) = σ k (S.orthogonalProjectionOnto u : S) := by
      refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS k hk _ (S.orthogonalProjectionOnto u).2) ?_
      intro w hw
      have hw' : σ k (σ k.conjTranspose w) = w := by
        rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ hk.1 _ hks.1, hk1, hσ.1.1]
        rfl
      rw [← hw', ← map_sub, hiso]
      exact S.starProjection_inner_eq_zero u _ (hS _ hks w hw)
    have h := hΘ k hk _ (S.orthogonalProjectionOnto u).2
    simpa [T, hP] using h
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v = ((⟨v, hv⟩ : S) : H) := rfl
  rw [hv', ← b.sum_repr ⟨v, hv⟩]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem i ?_)
  have := hY i T hT _ (hvY i)
  simpa [T] using this

end GlobalTheory.CompanionTheory.admitted

end
