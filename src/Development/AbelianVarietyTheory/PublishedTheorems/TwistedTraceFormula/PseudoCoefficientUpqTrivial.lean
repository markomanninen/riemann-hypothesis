module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv

@[expose] public section

open MeasureTheory GlobalTheory.Orb GlobalTheory.AdelicU Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.Published

def PseudoCoefficientUpq : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (σ : Matrix (Fin n) (Fin n) ℂ → (X →L[ℂ] X)) (h : GlobalTheory.Dec.IsSqIntIrr ε σ)
    (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsHaarMeasure],
    haveI := h.1
    ∃ f : Formalism.REAL.UJ ε → ℂ, IsBiFinite (Formalism.REAL.KG ε) f ∧ IsPseudoCoeff (ujMat ε) μ (ujRep h.2.2.1) f


end GlobalTheory.Published
