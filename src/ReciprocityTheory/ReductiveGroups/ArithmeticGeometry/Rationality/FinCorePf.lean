module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCoreSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DiscPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.UnitPointLiftBall

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

theorem finCore_holds : FinCoreStatement := by
  unfold FinCoreStatement
  intro K _ _ _ K₀ hK₀ S hS hSr hSu ι _ δ hδ hδ1 P b hPb hconv

  have step1 : ∀ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) → ‖MvPolynomial.eval x δ‖ = 1 →
      ∀ n, ‖MvPolynomial.eval x (P n)‖ ≤ 1 ∧ (n < 0 → MvPolynomial.eval x (P n) = 0) := by
    intro x hx hxδ
    have hd := disc_holds
    unfold DiscStatement at hd
    refine hd K K₀ hK₀ S hS hSr (fun n => MvPolynomial.eval x (P n)) b ?_ ?_
    · intro n hn
      show MvPolynomial.eval x (P n) = 0
      rw [hPb n hn, map_zero]
    · intro t ht
      refine ⟨(hconv t ht x hx hxδ).1, ?_⟩
      intro τ hτ hτ1
      exact (hconv (t * τ) (hSu t ht τ hτ hτ1) x hx hxδ).2

  have key : ∀ p : MvPolynomial ι K, p ≠ 0 → ∃ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) ∧
      ‖MvPolynomial.eval x δ‖ = 1 ∧ ∃ μ, ‖MvPolynomial.eval x p‖ = ‖AddMonoidAlgebra.coeff p μ‖ ∧
        AddMonoidAlgebra.coeff p μ ≠ 0 ∧ ∀ ν, ‖AddMonoidAlgebra.coeff p ν‖ ≤ ‖AddMonoidAlgebra.coeff p μ‖ := by
    intro p hp
    have hne : p.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      exact hp (MvPolynomial.support_eq_empty.mp h)
    obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image p.support
      (fun ν => ‖AddMonoidAlgebra.coeff p ν‖) hne
    have hc : AddMonoidAlgebra.coeff p μ ≠ 0 := MvPolynomial.mem_support_iff.mp hμ
    have hmax' : ∀ ν, ‖AddMonoidAlgebra.coeff p ν‖ ≤ ‖AddMonoidAlgebra.coeff p μ‖ := by
      intro ν
      by_cases hν : ν ∈ p.support
      · exact hmax ν hν
      · have h0 : AddMonoidAlgebra.coeff p ν = 0 := by
          simpa [MvPolynomial.mem_support_iff] using hν
        rw [h0, norm_zero]
        exact norm_nonneg _
    have hcpos : 0 < ‖AddMonoidAlgebra.coeff p μ‖ := norm_pos_iff.mpr hc
    have hQ : ∀ ν, ‖AddMonoidAlgebra.coeff (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p)
        ν‖ ≤ 1 := by
      intro ν
      rw [MvPolynomial.coeff_C_mul, norm_mul, norm_inv]
      calc ‖AddMonoidAlgebra.coeff p μ‖⁻¹ * ‖AddMonoidAlgebra.coeff p ν‖
          ≤ ‖AddMonoidAlgebra.coeff p μ‖⁻¹ * ‖AddMonoidAlgebra.coeff p μ‖ := by
            gcongr
            exact hmax' ν
        _ = 1 := inv_mul_cancel₀ hcpos.ne'
    have hQ1 : ∃ ν, ‖AddMonoidAlgebra.coeff (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p)
        ν‖ = 1 := by
      refine ⟨μ, ?_⟩
      rw [MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc, norm_one]
    obtain ⟨x, hx, hxQ, hxδ⟩ := UnitPointLiftBall.exists_unit_point K₀ hK₀
      (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p) δ hQ hQ1 hδ hδ1
    refine ⟨x, fun i => ⟨(hx i).1, (hx i).2.le⟩, hxδ, μ, ?_, hc, hmax'⟩
    have he : MvPolynomial.eval x p = AddMonoidAlgebra.coeff p μ *
        MvPolynomial.eval x (MvPolynomial.C (AddMonoidAlgebra.coeff p μ)⁻¹ * p) := by
      rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, mul_inv_cancel_left₀ hc]
    rw [he, norm_mul, hxQ, mul_one]
  intro n
  constructor
  · intro μ
    by_contra hlt
    push Not at hlt
    have hp : P n ≠ 0 := by
      intro h
      rw [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, norm_zero] at hlt
      linarith
    obtain ⟨x, hx, hxδ, ν, hev, -, hmax⟩ := key (P n) hp
    have h1 := (step1 x hx hxδ n).1
    rw [hev] at h1
    linarith [hmax μ]
  · intro hn
    by_contra hp
    obtain ⟨x, hx, hxδ, ν, hev, hc, -⟩ := key (P n) hp
    have h0 := (step1 x hx hxδ n).2 hn
    rw [h0, norm_zero] at hev
    exact hc (norm_eq_zero.mp hev.symm)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
