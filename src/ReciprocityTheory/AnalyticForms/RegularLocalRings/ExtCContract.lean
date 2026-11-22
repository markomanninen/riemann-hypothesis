module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial

variable {σ : Type} [Fintype σ]

theorem exists_linearForm_one : ∃ ℓ : ℂ →ₗ[ℚ] ℚ, ℓ 1 = 1 := by
  have h : ¬ ∀ φ : Module.Dual ℚ ℂ, φ 1 = 0 := by
    rw [Module.forall_dual_apply_eq_zero_iff]
    exact one_ne_zero
  push Not at h
  obtain ⟨φ, hφ⟩ := h
  exact ⟨(φ 1)⁻¹ • φ, by simp [hφ]⟩

noncomputable def projQ (ℓ : ℂ →ₗ[ℚ] ℚ) (q : MvPolynomial σ ℂ) : MvPolynomial σ ℚ :=
  ∑ m ∈ q.support, monomial m (ℓ (AddMonoidAlgebra.coeff q m))

theorem coeff_projQ (ℓ : ℂ →ₗ[ℚ] ℚ) (q : MvPolynomial σ ℂ) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (projQ ℓ q) m = ℓ (AddMonoidAlgebra.coeff q m) := by
  classical
  rw [projQ, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, map_zero]

theorem projQ_add (ℓ : ℂ →ₗ[ℚ] ℚ) (a b : MvPolynomial σ ℂ) :
    projQ ℓ (a + b) = projQ ℓ a + projQ ℓ b := by
  ext m
  simp [coeff_projQ]

theorem projQ_zero (ℓ : ℂ →ₗ[ℚ] ℚ) : projQ ℓ (0 : MvPolynomial σ ℂ) = 0 := by
  ext m
  simp [coeff_projQ]

theorem projQ_map (ℓ : ℂ →ₗ[ℚ] ℚ) (hℓ : ℓ 1 = 1) (g : MvPolynomial σ ℚ) :
    projQ ℓ (MvPolynomial.map (algebraMap ℚ ℂ) g) = g := by
  ext m
  rw [coeff_projQ, coeff_map]
  have : algebraMap ℚ ℂ (AddMonoidAlgebra.coeff g m) = AddMonoidAlgebra.coeff g m • (1 : ℂ) := by
    rw [Algebra.smul_def, mul_one]
  rw [this, map_smul, hℓ, smul_eq_mul, mul_one]

theorem projQ_map_mul (ℓ : ℂ →ₗ[ℚ] ℚ) (g : MvPolynomial σ ℚ) (h : MvPolynomial σ ℂ) :
    projQ ℓ (MvPolynomial.map (algebraMap ℚ ℂ) g * h) = g * projQ ℓ h := by
  classical
  ext m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_projQ, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_projQ]
  have : algebraMap ℚ ℂ (AddMonoidAlgebra.coeff g x.1) * AddMonoidAlgebra.coeff h x.2 = AddMonoidAlgebra.coeff g x.1 • AddMonoidAlgebra.coeff h x.2 := by
    rw [Algebra.smul_def]
  rw [this, map_smul, smul_eq_mul]

theorem comap_extC (I : Ideal (MvPolynomial σ ℚ)) :
    (extC I).comap (MvPolynomial.map (algebraMap ℚ ℂ)) = I := by
  obtain ⟨ℓ, hℓ⟩ := exists_linearForm_one
  refine le_antisymm ?_ Ideal.le_comap_map
  intro f hf
  have key : ∀ x ∈ extC I, ∀ h : MvPolynomial σ ℂ, projQ ℓ (h * x) ∈ I := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨g, hg, rfl⟩ h
      rw [mul_comm, projQ_map_mul]
      exact I.mul_mem_right _ hg
    · intro h
      rw [mul_zero, projQ_zero]
      exact I.zero_mem
    · intro a b _ _ ha hb h
      rw [mul_add, projQ_add]
      exact I.add_mem (ha h) (hb h)
    · intro a b _ hb h
      rw [smul_eq_mul, ← mul_assoc]
      exact hb (h * a)
  have := key _ hf 1
  rwa [one_mul, projQ_map ℓ hℓ] at this

end ReciprocityTheory.AnForm.R
