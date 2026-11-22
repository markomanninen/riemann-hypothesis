module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorEqTopOrLeKerFiniteLengthModulesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearTensorPolyVacuumPureTensorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCountableRank
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolActs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianTransform
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFourierTransform

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.HoweGlobal

theorem decomp {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {ι : Type} [Fintype ι] {M : ι → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (t : M₀ ⊗[ℂ] (⨂[ℂ] i, M i)) :
    ∃ (m : ℕ) (f : Fin m → M₀) (φ : Fin m → ∀ i, M i), t = ∑ j, f j ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (φ j) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul x y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod c φ =>
      refine ⟨1, fun _ => c • x, fun _ => φ, ?_⟩
      rw [Fin.sum_univ_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add y₁ y₂ h₁ h₂ =>
      obtain ⟨m₁, f₁, φ₁, e₁⟩ := h₁
      obtain ⟨m₂, f₂, φ₂, e₂⟩ := h₂
      refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_⟩
      rw [TensorProduct.tmul_add, e₁, e₂, Fin.sum_univ_add]
      simp
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨m₁, f₁, φ₁, e₁⟩ := h₁
    obtain ⟨m₂, f₂, φ₂, e₂⟩ := h₂
    refine ⟨m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, ?_⟩
    rw [e₁, e₂, Fin.sum_univ_add]
    simp

end GlobalTheory.HoweGlobal

end
