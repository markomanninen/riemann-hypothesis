module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagMapChernRootsPointPoly
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmChernRootsMulFibrePoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralEqFlagDegreeWeight

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

noncomputable section

namespace GlobalTheory.GrassTop

theorem intGr_pointPoly : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
    intGr H Dw (pointPoly H Dw) = 1 := by
  intro E _ _ _ H Dw
  unfold intGr
  have rename_chernRoots (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ)))
      (R : MvPolynomial (ι × ℕ) ℝ) :
      rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (chernRoots m R) = chernRoots m R := by
    have h : (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))).comp (chernRoots m) = chernRoots m := by
      apply MvPolynomial.algHom_ext
      intro x
      simp only [AlgHom.comp_apply, chernRoots, aeval_X, rename_rename]
      have e : ((fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) ∘ Sigma.mk x.1) = Sigma.mk x.1 ∘ (w x.1) := by
        funext i; rfl
      rw [e, ← rename_rename, rename_esymm]
    exact AlgHom.congr_fun h R

  have antisymm_chernRoots_mul (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ)
      (Q : MvPolynomial (Root m) ℝ) : antisymm (chernRoots m R * Q) = chernRoots m R * antisymm Q := by
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, rename_chernRoots, mul_smul_comm]

  have prod_Ioi_rev {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev i) - v (Fin.rev j))) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
    have h : ∀ f : Fin N → Fin N → R, (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
        ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 := by
      intro f
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      congr 1
      ext j; simp
    rw [h, h, ← Fintype.prod_prod_type' (f := fun i j => if i < j then v (Fin.rev i) - v (Fin.rev j) else 1),
      ← Fintype.prod_prod_type' (f := fun i j => if i < j then v j - v i else 1)]
    refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ fun p => ?_
    simp [Fin.rev_lt_rev]

  have sum_sign_prod_neg_pow {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ))) =
        ∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i) := by
    let M : Matrix (Fin N) (Fin N) R := Matrix.of fun j i => (-v j) ^ (N - 1 - (i : ℕ))
    have h1 : M.det = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ)) := by
      rw [Matrix.det_apply']
      rfl
    have h2 : M.submatrix Fin.revPerm Fin.revPerm = Matrix.vandermonde (fun j => -v (Fin.rev j)) := by
      ext j i
      simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
      congr 1
      omega
    rw [← h1, ← Matrix.det_submatrix_equiv_self Fin.revPerm, h2, Matrix.det_vandermonde,
      GlobalTheory.GoodMetric.RootDiscrPerm.prod_Iio_eq_det, Matrix.det_vandermonde]
    simp only [neg_sub_neg]
    exact prod_Ioi_rev v

  have antisymm_fibrePoint (ι : Type) [Fintype ι] (m : ι → ℕ) : antisymm (fibrePoint m) = rootDiscr m := by
    have hw : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)),
        ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (fibrePoint m) =
          ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(X (⟨τ, w τ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))) := by
      intro w
      unfold fibrePoint
      rw [map_prod, Fintype.prod_sigma, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [map_pow, map_neg, rename_X]
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.sum_congr rfl fun w _ => hw w]
    rw [← Fintype.prod_sum (fun τ (σ : Equiv.Perm (Fin (m τ))) => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(X (⟨τ, σ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))))]
    unfold GlobalTheory.GoodMetric.rootDiscr
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact sum_sign_prod_neg_pow (fun i : Fin (m τ) => (X (⟨τ, i⟩ : Root m) : MvPolynomial (Root m) ℝ))
  have h : antisymm (chernRoots Dw.mult (pointPoly H Dw) * fibrePoint Dw.mult) =
      chernRoots Dw.mult (pointPoly H Dw) * rootDiscr Dw.mult := by
    rw [antisymm_chernRoots_mul, antisymm_fibrePoint]
  rw [← h, degFl_rho_antisymm, prod_factorial_mult,
    rho_eq_flagMap, ← GlobalTheory.Schubert.schubGam_apply, GlobalTheory.SchubertPoint.schubGam_pointPoly, mul_one]
  have hne : ((Dw.p.factorial * Dw.q.factorial : ℝ) ^ Fintype.card (GlobalTheory.AllWt.Psi H)) ≠ 0 := by
    apply pow_ne_zero
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _) (by exact_mod_cast Nat.factorial_ne_zero _)
  exact div_self hne

end GlobalTheory.GrassTop
