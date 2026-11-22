module

public import Mathlib
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Formalism.PeriodIntegrals.DSInfCharCap
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerived
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVecUnitaryModule
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.KFiniteVectorsIrreducibleUnitaryUnitaryGroupPQ

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.KFinSmoothBoth

theorem kFin_smooth_both : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsHCParam lam →
    Formalism.MainNotions.S.IsDS ε lam σ → ∀ v : H, Formalism.MainNotions.S.IsKFin ε σ v →
    v ∈ GlobalTheory.SmoothVecMod.smoothVec ε σ ∧ v ∈ PI.PhMeasCore.smoothVecs (Formalism.REAL.Jm ε) σ := by
  intro n ε lam H _ _ σ _ hσ v hv
  have : CompleteSpace H := hσ.1
  have h : Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) fun g => σ g v :=
    GlobalTheory.Published.KFiniteVectorsUnitary.smoothOnH
      GlobalTheory.CompanionTheory.Published.kFiniteVectors_irreducibleUnitary_unitaryGroupPQ
      hσ.2.2.1 hσ.2.2.2.1 hv
  exact ⟨h, h⟩

end GlobalTheory.CompanionTheory.KFinSmoothBoth
