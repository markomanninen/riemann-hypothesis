module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPairingChartPartialDerivativeModMax
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegreeLt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstRestrictSumVariables

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_pairing_chart_partial_derivative_mod_max : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m → ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) → ∀ (ψ : G.A n →ₗ[O] O) (H : MvPowerSeries (Fin d ⊕ Fin d) O), LinearMap.mul' O O (TensorProduct.map ψ φ.ofConv (c.ev₂ n H)) - ψ (c.ev n (∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) H))) ∈ m := by
  intro p O _ G d c n m hp u φ hφ ψ H
  have hCoeff (T : MvPowerSeries (Fin d ⊕ Fin d) O) (i : Fin d) (α : Fin d →₀ ℕ) :
      coeff α (atZero (pderiv (R := O) (Sum.inr i) T)) =
        coeff (α.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) T := by
    rw [atZero, (coeff_subst_restrict_sum _).1, coeff_pderiv,
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
    simp
  have hMonomial (α β : Fin d →₀ ℕ) (i : Fin d) :
      atZero (pderiv (R := O) (Sum.inr i) (monomial (α.sumElim β) (1 : O))) =
        lin (monomial β (1 : O)) i • monomial α (1 : O) := by
    classical
    ext γ
    rw [hCoeff, map_smul, lin, coeff_monomial, coeff_monomial, coeff_monomial]
    have hγ : γ.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 =
        γ.sumElim (Finsupp.single i 1) := by
      rw [Finsupp.sumElim_eq_add, Finsupp.mapDomain_single]
    rw [hγ]
    have h : γ.sumElim (Finsupp.single i 1) = α.sumElim β ↔
        γ = α ∧ Finsupp.single i 1 = β := by
      constructor
      · intro h
        exact ⟨Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inl j),
          Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inr j)⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    simp only [h]
    by_cases hα : γ = α <;> by_cases hβ : Finsupp.single i 1 = β <;> simp [hα, hβ]
  obtain ⟨N₁, h₁⟩ := (c.isEval n).2 1
  obtain ⟨N₂, h₂⟩ := (c.isEval₂ n).2 1
  have hs : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ : Fin d => 0)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)
  let D : MvPowerSeries (Fin d ⊕ Fin d) O →ₗ[O] MvPowerSeries (Fin d) O :=
    ∑ i, u i • ((substAlgHom hs).toLinearMap ∘ₗ (pderiv (R := O) (Sum.inr i)).toLinearMap)
  have hD : ∀ H, D H = ∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) H) := fun H => by
    simp [D, atZero, LinearMap.sum_apply, coe_substAlgHom]
  let P : G.A n ⊗[O] G.A n →ₗ[O] O := LinearMap.mul' O O ∘ₗ TensorProduct.map ψ φ.ofConv
  let L : MvPowerSeries (Fin d ⊕ Fin d) O →ₗ[O] O :=
    P ∘ₗ (c.ev₂ n).toLinearMap - ψ ∘ₗ (c.ev n).toLinearMap ∘ₗ D
  have hL : ∀ H, L H = P (c.ev₂ n H) - ψ (c.ev n (∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) H))) :=
    fun H => by rw [← hD]; rfl
  have key := GlobalTheory.PairingEv.mem_of_monomial_mem_of_tail_mem (Submodule.comap L m) (N₁ + N₂ + 1) ?_ ?_ H
  · rw [Submodule.mem_comap, hL] at key
    exact key
  · intro γ
    rw [Submodule.mem_comap, hL, ← Finsupp.comapDomain_sumElim_comapDomain γ]
    generalize Finsupp.comapDomain Sum.inl γ _ = α
    generalize Finsupp.comapDomain Sum.inr γ _ = β
    rw [GlobalTheory.PairingEv.chart_ev₂_monomial]
    simp only [hMonomial, smul_smul, ← Finset.sum_smul, map_smul, smul_eq_mul]
    have := m.mul_mem_left (ψ (c.ev n (monomial α 1))) (hφ (monomial β 1))
    convert this using 1
    have e : P (c.ev n (monomial α 1) ⊗ₜ[O] c.ev n (monomial β 1)) =
        ψ (c.ev n (monomial α 1)) * φ (c.ev n (monomial β 1)) := by
      simp only [P, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [e]; ring
  · intro T hT
    rw [Submodule.mem_comap, hL]
    obtain ⟨a, ha⟩ := h₂ T fun α hα => hT α (by omega)
    obtain ⟨b, hb⟩ := h₁ (∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) T)) fun α hα => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, hCoeff, hT, smul_zero]
      rw [map_add (f := _), Finsupp.degree_mapDomain, Finsupp.degree_single]
      omega
    rw [ha, hb, pow_one, pow_one, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul, map_nsmul,
      nsmul_eq_mul, nsmul_eq_mul]
    exact m.sub_mem (m.mul_mem_right _ hp) (m.mul_mem_right _ hp)
