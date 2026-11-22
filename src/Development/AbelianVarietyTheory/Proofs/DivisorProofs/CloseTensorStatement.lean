module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTensor
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.close_comp_of_close_includeRight : ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C) (ρ : Hol W →+* R ⊗[ℂ] Hol W₀), (∀ (a : Fin g) (h : Hol W), ρ (dw a h) = LinearMap.lTensor R (dw a).toLinearMap (ρ h)) → ∀ ψ₁ ψ₂ : R ⊗[ℂ] Hol W₀ →+* C, (∀ d : R, ψ₁ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) → Close J (ψ₁.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) → Close J (ψ₁.comp ρ) (ψ₂.comp ρ) := by
  exact @GlobalTheory.CloseTen.close_tensor
