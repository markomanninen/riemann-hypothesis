module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteBasisAlgebraicForms

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.latFacts_pf :
    UpperTheory.Gal.Gen.LatFacts := by
  classical
  intro l _ ι σ V _
  refine ⟨fun φ => ?_, fun x => ?_⟩
  · let B := Module.finBasis ℂ V
    open MvPolynomial in
    have h : ∀ i, ∃ (s : Finset (σ →₀ ℕ)) (a : s → ℂ), ∀ v : V,
        B.repr v i = ∑ m : s, a m * AddMonoidAlgebra.coeff (v : MvPolynomial σ ℂ) m.1 := by
      intro i
      classical
      let s : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun j => ((B j : V) : MvPolynomial σ ℂ).support
      let R : V →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun m => (lcoeff ℂ m.1).comp V.subtype
      have hR : LinearMap.ker R = ⊥ := by
        refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
        have h0 : ∀ m : s, AddMonoidAlgebra.coeff (v : MvPolynomial σ ℂ) m.1 = 0 := fun m => congrFun hv m
        refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
        by_cases hm : m ∈ s
        · simpa using h0 ⟨m, hm⟩
        · have hv' : (v : MvPolynomial σ ℂ) = ∑ j, B.repr v j • ((B j : V) : MvPolynomial σ ℂ) := by
            calc (v : MvPolynomial σ ℂ) = ((∑ j, B.repr v j • B j : V) : MvPolynomial σ ℂ) := by rw [B.sum_repr v]
              _ = _ := by rw [Submodule.coe_sum]; rfl
          rw [hv', coeff_sum]
          simp only [coeff_smul, ZeroMemClass.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
          refine Finset.sum_eq_zero fun j _ => ?_
          have : m ∉ ((B j : V) : MvPolynomial σ ℂ).support := fun h =>
            hm (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, h⟩)
          rw [notMem_support_iff.1 this, smul_zero]
      obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hR
      refine ⟨s, fun m => B.repr (L (Pi.single m 1)) i, fun v => ?_⟩
      have e1 : B.repr v i = ((B.coord i).comp L) (R v) := by
        rw [LinearMap.comp_apply, ← LinearMap.comp_apply L R, hL, LinearMap.id_apply, Module.Basis.coord_apply]
      rw [e1, LinearMap.pi_apply_eq_sum_univ ((B.coord i).comp L) (R v)]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hs : (fun j => if m = j then (1 : ℂ) else 0) = Pi.single m 1 := by
        funext j
        simp [Pi.single_apply, eq_comm]
      rw [hs, smul_eq_mul, mul_comm]
      rfl
    choose s a ha using h
    refine ⟨∑ i, ∑ m : s i, ‖ι.symm (a i m)‖ * ‖ι.symm (φ (B i))‖,
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun m _ => mul_nonneg (norm_nonneg _) (norm_nonneg _),
      fun R x hx => ?_⟩
    have e : φ x = ∑ i, B.repr x i * φ (B i) := by
      have h := congrArg φ (B.sum_repr x)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    have h1 : ∀ i, ‖ι.symm (B.repr x i)‖ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ha i x, map_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [map_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_mul, norm_mul, Finset.sum_mul]
    calc _ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R * ‖ι.symm (φ (B i))‖ :=
          mul_le_mul_of_nonneg_right (h1 i) (norm_nonneg _)
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by ring
  · have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by linarith)
    set T : ℝ := ∑ m ∈ x.1.support, ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖ + 1 with hTdef
    have hS : 0 ≤ ∑ m ∈ x.1.support, ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖ :=
      Finset.sum_nonneg fun m _ => norm_nonneg _
    have hT : 0 < T := by linarith
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hT) (inv_lt_one_of_one_lt₀ hl)
    have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    refine ⟨(l : ℂ) ^ k, pow_ne_zero _ hlc, fun m => ?_⟩
    have hnl : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
      have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
      rw [map_natCast, Padic.norm_p] at h
      exact h
    have hn : ‖ι.symm ((l : ℂ) ^ k)‖ = ((l : ℝ)⁻¹) ^ k := by
      rw [map_pow, map_natCast, norm_pow, hnl]
    have hc : ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖ ≤ T := by
      by_cases hm : m ∈ x.1.support
      · have := Finset.single_le_sum (f := fun m => ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖)
          (fun m _ => norm_nonneg _) hm
        linarith
      · rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, norm_zero]
        exact hT.le
    have e : AddMonoidAlgebra.coeff (((l : ℂ) ^ k • x : V) : MvPolynomial σ ℂ) m =
        (l : ℂ) ^ k * AddMonoidAlgebra.coeff x.1 m := by
      rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    rw [e, map_mul, norm_mul, hn]
    calc _ ≤ ((l : ℝ)⁻¹) ^ k * T := mul_le_mul_of_nonneg_left hc (pow_nonneg hl0.le _)
      _ ≤ T⁻¹ * T := mul_le_mul_of_nonneg_right hk.le hT.le
      _ = 1 := inv_mul_cancel₀ hT.ne'
