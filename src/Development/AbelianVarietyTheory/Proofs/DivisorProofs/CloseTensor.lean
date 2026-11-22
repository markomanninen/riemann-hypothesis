module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroMoveTensorHolomorphicStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CloseTen

theorem baseChange_tensor_holomorphic_closeness {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
    {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C)
    (ρ : Hol W →+* R ⊗[ℂ] Hol W₀)
    (hρ : ∀ (a : Fin g) (h : Hol W),
      ρ (dw (W := W) a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h))
    (ψ₂ : R ⊗[ℂ] Hol W₀ →+* C) (ρ₁ : Hol W₀ →+* C)
    (hc : Close J ρ₁ (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom)) :
    ∀ φ : R ⊗[ℂ] Hol W₀ →+* C,
      (∀ h : Hol W₀, φ ((1 : R) ⊗ₜ[ℂ] h) = ρ₁ h) →
      (∀ d : R, φ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) → Close J (φ.comp ρ) (ψ₂.comp ρ) := by
  induction hc using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro φ hφ hφd
    have e : φ = ψ₂ := by
      apply RingHom.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul d h =>
        have e1 : d ⊗ₜ[ℂ] h = (d ⊗ₜ[ℂ] (1 : Hol W₀)) * ((1 : R) ⊗ₜ[ℂ] h) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
        rw [e1, map_mul, map_mul, hφd, hφ]
        rfl
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    subst e
    exact Relation.ReflTransGen.refl
  | head hs _ ih =>
    intro φ hφ hφd
    obtain ⟨n, hnJ, hn2, hn⟩ := hs
    have hMove : ∃ φ' : R ⊗[ℂ] Hol W₀ →+* C, ∀ x,
        φ' x = φ x + ∑ a, φ (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap x) * n a :=
      GlobalTheory.SqZeroMove.gen_hom φ
        (fun a => (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap).toAddMonoidHom)
        (fun a => GlobalTheory.SqZeroMove.lTensor_one (R := R) (dw (W := W₀) a))
        (fun a x y => GlobalTheory.SqZeroMove.lTensor_leibniz (dw (W := W₀) a) x y) n hn2
    obtain ⟨φ', hφ'⟩ := hMove
    refine Relation.ReflTransGen.head ⟨n, hnJ, hn2, fun h => ?_⟩ (ih φ' (fun h => ?_) (fun d => ?_))
    · rw [RingHom.comp_apply, hφ']
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [RingHom.comp_apply, hρ]
    · rw [hφ', hn h, hφ]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.lTensor_tmul, Derivation.coeFn_coe, hφ]
    · rw [hφ', ← hφd]
      conv_rhs => rw [← add_zero (φ (d ⊗ₜ[ℂ] 1))]
      congr 1
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [LinearMap.lTensor_tmul, Derivation.coeFn_coe, Derivation.map_one_eq_zero,
        TensorProduct.tmul_zero, map_zero, zero_mul]

theorem close_tensor :
    ∀ {I : Type} [Fintype I] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot Empty g)}
      {R : Type} [CommRing R] [Algebra ℂ R] {C : Type} [CommRing C] (J : Ideal C)
      (ρ : Hol W →+* R ⊗[ℂ] Hol W₀),
      (∀ (a : Fin g) (h : Hol W),
        ρ (dw (W := W) a h) = LinearMap.lTensor R (dw (W := W₀) a).toLinearMap (ρ h)) →
      ∀ ψ₁ ψ₂ : R ⊗[ℂ] Hol W₀ →+* C,
        (∀ d : R, ψ₁ (d ⊗ₜ[ℂ] 1) = ψ₂ (d ⊗ₜ[ℂ] 1)) →
        Close J (ψ₁.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom)
          (ψ₂.comp (Algebra.TensorProduct.includeRight : Hol W₀ →ₐ[ℂ] R ⊗[ℂ] Hol W₀).toRingHom) →
        Close J (ψ₁.comp ρ) (ψ₂.comp ρ) := by
  intro I _ g W W₀ R _ _ C _ J ρ hρ ψ₁ ψ₂ hd hc
  exact baseChange_tensor_holomorphic_closeness J ρ hρ ψ₂ _ hc ψ₁ (fun h => rfl) hd

end GlobalTheory.CloseTen
