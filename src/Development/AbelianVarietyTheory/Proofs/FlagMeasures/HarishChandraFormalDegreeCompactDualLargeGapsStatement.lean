module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraFormalDegreeCompactDualLargeGaps
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLitG
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S MeasureTheory

theorem _root_.GlobalTheory.T.harishChandra_formalDegree_compactDual_large_gaps : ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal),
    (∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)}) →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (h : ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
      (∃ a, ε a = true) → (∃ a, ε a = false) → Formalism.QuantumDeterminants.GapAtLeast ε lam h → Formalism.MainNotions.GapDS.thrE ε + 1 < h →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
        IsFdeg ((sc N ε : ENNReal) • Formalism.REAL.muG ε) σ (Formalism.QuantumDeterminants.fdegHC lam) :=
  GlobalTheory.FdegGap.fdeg_gap
