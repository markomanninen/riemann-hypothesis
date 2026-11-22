module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MatrixCoefficientFrameChangeDiscreteSeries
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_frame_change_discrete_series : GlobalTheory.Published.DiscreteSeriesUpqUnique → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ),
    Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsDS ε lam σ → IsDS ε lam σ' →
    ∀ (P P' G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → IsUnit P' → Pᴴ * Formalism.REAL.Jm ε * P = G →
      P'ᴴ * Formalism.REAL.Jm ε * P' = G →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (ℓ : H' →ₗ[ℂ] ℂ) (v : H'), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ' ℓ →
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ' v → (∀ y ∈ UJset ε, F (P'⁻¹ * y * P') = ℓ (σ' y v)) →
    ∃ (ℓ' : H →ₗ[ℂ] ℂ) (v' : H), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ' ∧
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ v' ∧ ∀ y ∈ UJset ε, F (P⁻¹ * y * P) = ℓ' (σ y v') := by
  first | exact @GlobalTheory.TypeSum.FrameChange.coef_frame_change | exact GlobalTheory.TypeSum.FrameChange.coef_frame_change | (intros; apply GlobalTheory.TypeSum.FrameChange.coef_frame_change <;> assumption)
