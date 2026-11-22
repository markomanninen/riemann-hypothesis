module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicNormDegreeEqPadicNormDetTateModuleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetAevalEqProdArootsCharpolyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNormProdAevalEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativePolynomialFunctionEqNormFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneousStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDimStatement

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

theorem map_eq_charpoly_vmap : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 →
    ∀ (A : AbVar K) [Module.Finite ℚ_[l] (Vl l A)] (f : End A) (P : Polynomial ℚ),
    P.Monic → P.natDegree = 2 * A.dim →
    (∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f).asHom : ℚ)) →
    P.map (algebraMap ℚ ℚ_[l]) = (vmap l (A := A) (B := A) f.asHom).charpoly := by
  intro K _ l _ hl A _ f P hPm hPd hP
  obtain ⟨hfree, hfin, -, -, hrkV⟩ := GlobalTheory.T.tateModule_free_finrank_two_mul_dim K l hl A
  let δ : Polynomial ℤ → ℚ := fun F => (deg (A := A) (B := A) (Polynomial.aeval f F).asHom : ℚ)
  have hmul : ∀ F G, δ (F * G) = δ F * δ G := by
    intro F G
    simp only [δ, map_mul]
    rw [End.mul_asHom, (GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul K A A A _ _ rfl rfl).2]
    push_cast
    exact mul_comm _ _
  have hpoly : ∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * A.dim) ∧
      ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i) := by
    intro n u
    obtain ⟨Φ, hΦ, hΦe⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl n (fun i => (Polynomial.aeval f (u i)).asHom)
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦe m]
    have hz (k : ℤ) (g : End A) : (k • g).asHom = k • g.asHom :=
      map_zsmul End.addEquiv k g
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [δ, map_sum, map_zsmul, End.sum_asHom, hz]
  have hPn : ∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X) := by
    intro n
    rw [hP n]
    simp only [δ, map_sub, map_intCast, Polynomial.aeval_X, eq_intCast]
  have hroots := GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm (PadicAlgCl l) A.dim δ P hmul hpoly hPm hPd hPn
  apply GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq l
  · exact hPm.map _
  · exact LinearMap.charpoly_monic _
  · rw [Polynomial.natDegree_map, hPd, LinearMap.charpoly_natDegree, hrkV]
  · intro F
    have h1 : (P.map (algebraMap ℚ ℚ_[l])).aroots (PadicAlgCl l) = P.aroots (PadicAlgCl l) := by
      simp only [Polynomial.aroots, Polynomial.map_map]
      congr 2
    rw [h1]
    refine (congrArg norm (hroots F)).symm.trans ?_
    have h2 := GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' ℚ_[l] (PadicAlgCl l) (Vl l A) (vmap l f.asHom) (F.map (algebraMap ℤ ℚ_[l]))
    simp only [Polynomial.aeval_map_algebraMap] at h2
    rw [← h2]
    let t : End A →+* Module.End ℤ_[l] (Tl l A) :=
      { toFun := fun g => tmap l A A g.asHom
        map_one' := tmap_id l A
        map_mul' := fun g h => tmap_comp l h.asHom g.asHom
        map_zero' := map_zero (tmap l A A)
        map_add' := fun g h => map_add (tmap l A A) g.asHom h.asHom }
    let ψ : End A →+* Module.End ℚ_[l] (Vl l A) :=
      (Module.End.baseChangeHom ℤ_[l] ℚ_[l] (Tl l A)).toRingHom.comp t
    have hψ : vmap l (A := A) (B := A) f.asHom = ψ f := rfl
    have hev : ∀ G : Polynomial ℤ, Polynomial.aeval (ψ f) G = ψ (Polynomial.aeval f G) := by
      intro G
      induction G using Polynomial.induction_on with
      | C a => simp
      | add p q hp hq => simp only [map_add (f := _), hp, hq]
      | monomial n a _ => simp only [map_mul, map_pow, Polynomial.aeval_X, eq_intCast, map_intCast]
    rw [hψ, hev F]
    have h3 : ψ (Polynomial.aeval f F) = (tmap l A A (Polynomial.aeval f F).asHom).baseChange ℚ_[l] := rfl
    rw [h3, LinearMap.det_baseChange, PadicAlgCl.norm_extends]
    have h4 (g : A ⟶ A) : ‖(deg g : ℤ_[l])‖ = ‖LinearMap.det (tmap l A A g)‖ := by
      by_cases hg : IsIsogeny g
      · obtain ⟨-, -, hpos, -⟩ := isogeny_flat_finrank K A A g hg
        obtain ⟨-, hcard⟩ := GlobalTheory.T.tateModuleMap_injective_card_coker_of_isogeny K l hl A A g hg
        rw [GlobalTheory.T.norm_det_eq_inv_card_coker l (Tl l A) (tmap l A A g) _ hcard,
          norm_natCast_padicInt l hpos.ne']
      · have hdeg : deg g = 0 := by simp [deg, hg]
        rw [hdeg, Nat.cast_zero, norm_zero, eq_comm, norm_eq_zero]
        by_contra hne
        apply hg
        rw [(GlobalTheory.T.isFinite_iff_tateModuleMap_injective_and_isogeny_iff K l hl A A g).2]
        have hu : IsUnit (LinearMap.det (vmap l g)) := by
          rw [vmap, LinearMap.det_baseChange]
          exact (isUnit_iff_ne_zero).2
            ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective ℤ_[l] ℚ_[l])).2 hne)
        rw [← LinearMap.isUnit_iff_isUnit_det] at hu
        exact (Module.End.isUnit_iff _).1 hu
    have h5 : algebraMap ℚ (PadicAlgCl l) (δ F) = algebraMap ℚ_[l] (PadicAlgCl l) ((deg (A := A) (B := A) (Polynomial.aeval f F).asHom : ℕ) : ℚ_[l]) := by
      simp only [δ, map_natCast]
    rw [h5, PadicAlgCl.norm_extends]
    simpa only [PadicInt.norm_def, PadicInt.coe_natCast, PadicInt.algebraMap_apply] using
      h4 (Polynomial.aeval f F).asHom

end GlobalTheory.AV.AbVar
