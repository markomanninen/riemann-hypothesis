module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousCA
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddEquivAddHaarCharProdCongr
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.LeviModulus
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ImaginaryModulus

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_anti {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ δ : E, δ ≠ 0 ∧ σ δ = -δ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases hx : ∃ x, σ x ≠ x
  · obtain ⟨x, hx⟩ := hx
    refine ⟨x - σ x, sub_ne_zero.2 (Ne.symm hx), ?_⟩
    rw [map_sub, sig_sig h]; ring
  · push_neg at hx
    exfalso
    have hr : ComplexEmbedding.IsReal τ := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      rw [ComplexEmbedding.conjugate_coe_eq]
      have := h.2.2.2 τ x
      rw [hx x] at this
      exact this.symm
    exact InfinitePlace.isComplex_mk_iff.1 (h.2.1.isComplex _) hr

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => simp [cA, sigR]

section Iso

variable (σ : E →ₐ[F] E) [IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))]

end Iso


end GlobalTheory.ImaginaryModulus
