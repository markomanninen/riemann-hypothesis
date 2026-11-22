module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HomologyRestrictScalarsBijective
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CubeComplexGradedModuleExactAtOfLargeDegree

@[expose] public section

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial

namespace GlobalTheory

theorem weightedHomogeneousComponent_one_int {σ A : Type*} [CommRing A] (F : MvPolynomial σ A)
    (m : ℤ) : weightedHomogeneousComponent (fun _ : σ => (1 : ℤ)) m F =
      if 0 ≤ m then homogeneousComponent m.toNat F else 0 := by
  ext a
  rw [coeff_weightedHomogeneousComponent, weight_one_int]
  by_cases hm : 0 ≤ m
  · rw [if_pos hm, coeff_homogeneousComponent]
    by_cases h : (a.degree : ℤ) = m
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  · rw [if_neg hm, if_neg (by omega)]
    simp

theorem isHomogeneous_polyGrading_of_component {ι A : Type} [CommRing A]
    (J : Ideal (MvPolynomial ι A))
    (hJ : ∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) :
    (J : Submodule (MvPolynomial ι A) (MvPolynomial ι A)).IsHomogeneous (polyGrading ι A) := by
  intro m F hF
  have e : (decompose (polyGrading ι A) F m : MvPolynomial ι A) =
      weightedHomogeneousComponent (fun _ : ι => (1 : ℤ)) m F :=
    weightedDecomposition.decompose'_apply A _ F m
  rw [e, weightedHomogeneousComponent_one_int]
  split_ifs
  · exact hJ F hF _
  · exact zero_mem _

universe u

private theorem grAug_bijective_iff_local (ι : Type) {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M)
    [PolyGradedSMul ι ℳ] [LinearOrder ι] (n : ℤ) :
    Function.Bijective (grAug (ι := ι) (ℳ := ℳ) n) ↔
      (cubeComplex (grCube ι ℳ n)).ExactAt 0 ∧
        (cubeComplex (grCube ι ℳ n)).ExactAt 1 := by
  rw [← isIso_cechAugHomology_iff, ConcreteCategory.isIso_iff_bijective]
  exact Function.Bijective.of_comp_iff (cechAugHomology (grCube ι ℳ n)).hom
    (g := toHomLoc ℳ ∅ n) (homLocEmptyEquiv (ι := ι) ℳ n).bijective

private theorem cechHomologyZeroIso_grAug_local (ι : Type) {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M)
    [PolyGradedSMul ι ℳ] [LinearOrder ι] (n : ℤ) (m : ℳ n)
    (s : {s : Finset ι // s.card = 1}) :
    ((cechHomologyZeroIso (grCube ι ℳ n)).hom.hom
      (grAug (ι := ι) (ℳ := ℳ) n m)).1 s = toHomLoc ℳ s.1 n m := by
  exact (congrFun congr(($(cechAugHomology_comp (grCube ι ℳ n))).hom
    (toHomLoc ℳ ∅ n m)) s).trans (homLocRes_toHomLoc ℳ _ n m)

theorem sum_cubeSign_pair {ι : Type} [LinearOrder ι] {t : Finset ι} (ht : t.card = 2) :
    ∑ i ∈ t, cubeSign t i = 0 := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 ht
  rw [Finset.sum_pair hab]
  have h := cubeSign_mul_erase (t := {a, b}) (by simp) (by simp) hab
  rw [Finset.erase_insert (by simpa using hab), Finset.pair_comm,
    Finset.erase_insert (by simpa using hab.symm), cubeSign_singleton, cubeSign_singleton,
    mul_one, mul_one, Finset.pair_comm] at h
  rw [h]; ring

theorem exists_form_of_compatible_fractions : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) A)), (∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (N : ℕ) (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i, (F i).IsHomogeneous (d + N)) → (∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j) ^ L * (X j ^ N * F i - X i ^ N * F j) ∈ J) → ∃ G : MvPolynomial (Fin (n + 1)) A, G.IsHomogeneous d ∧ ∀ i, ∃ L : ℕ, (X i : MvPolynomial (Fin (n + 1)) A) ^ L * (F i - X i ^ N * G) ∈ J := by
  intro A _ _ n J hJ
  letI : Decomposition (grQuot (polyGrading (Fin (n + 1)) A) J) :=
    grQuotDecomposition _ (isHomogeneous_polyGrading_of_component J hJ)
  obtain ⟨n₀, hn₀⟩ := cubeComplex_grCube_exactAt_of_finite (Fin (n + 1)) A (MvPolynomial (Fin (n + 1)) A ⧸ J)
    (grQuot (polyGrading (Fin (n + 1)) A) J) inferInstance
  refine ⟨n₀.toNat, fun d hd N F hF hc => ?_⟩
  have hd' : n₀ ≤ (d : ℤ) := by omega
  have hb := (grAug_bijective_iff_local (ι := Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J)
    (d : ℤ)).2 ⟨hn₀ d hd' 0, hn₀ d hd' 1⟩
  have hmem : ∀ i, awayFrac (MvPolynomial (Fin (n + 1)) A ⧸ J) (xProd (R := A) {i}) N
      (Submodule.Quotient.mk (F i)) ∈ homLoc (grQuot (polyGrading (Fin (n + 1)) A) J) {i} d :=
    fun i => awayFrac_mem_homLoc (ℳ := grQuot (polyGrading (Fin (n + 1)) A) J) (d := ((d + N : ℕ) : ℤ))
      ⟨F i, mem_polyGrading_natCast.2 (hF i), rfl⟩ (by simp)
  let y : ∀ i, (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d).obj {i} :=
    fun i => ⟨_, hmem i⟩
  let x := Cube.termOneEquiv (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d) y

  have hres : ∀ (s : {s : Finset (Fin (n + 1)) // s.card = 1}) (T : Finset (Fin (n + 1)))
      (h : s.1 ⊆ T), ∃ j ∈ s.1, (show homLoc (grQuot (polyGrading (Fin (n + 1)) A) J) T d from
        Cube.res (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d) h (x s)).1 =
        awayFrac (MvPolynomial (Fin (n + 1)) A ⧸ J) (xProd (R := A) T) N
          (xProd (R := A) (T.erase j) ^ N • Submodule.Quotient.mk (F j)) := by
    rintro ⟨s, hs⟩ T h
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.1 hs
    refine ⟨j, Finset.mem_singleton_self j, ?_⟩
    have hj : j ∈ T := h (Finset.mem_singleton_self j)
    have e : x ⟨{j}, hs⟩ = y j := Cube.termOneEquiv_apply _ y j
    simp only [e, res_grCube]
    erw [coe_homLocRes]
    exact locRes_awayFrac X h (by rw [Finset.prod_singleton, Finset.prod_erase_mul _ _ hj]) N _

  have hx : Cube.d (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d) 1 x = 0 := by
    funext t
    obtain ⟨a, b, hab, hab'⟩ := Finset.card_eq_two.1 t.2
    have hv : ∀ j ∈ t.1, awayFrac (MvPolynomial (Fin (n + 1)) A ⧸ J) (xProd (R := A) t.1) N
        (xProd (R := A) (t.1.erase j) ^ N • Submodule.Quotient.mk (F j)) =
        awayFrac (MvPolynomial (Fin (n + 1)) A ⧸ J) (xProd (R := A) t.1) N
        (xProd (R := A) (t.1.erase a) ^ N • Submodule.Quotient.mk (F a)) := by
      intro j hj
      rw [hab'] at hj ⊢
      rcases Finset.mem_insert.1 hj with rfl | hj
      · rfl
      · rw [Finset.mem_singleton] at hj
        subst hj
        have e1 : ({a, j} : Finset (Fin (n + 1))).erase j = {a} := by
          ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; aesop
        have e2 : ({a, j} : Finset (Fin (n + 1))).erase a = {j} := by
          ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]; aesop
        rw [e1, e2]
        simp only [xProd, Finset.prod_singleton, Finset.prod_pair hab]
        rw [awayFrac_eq_iff]
        obtain ⟨L, hL⟩ := hc a j
        refine ⟨L, ?_⟩
        rw [smul_smul, smul_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
          Submodule.Quotient.eq]
        have := J.mul_mem_left (-((X a * X j) ^ N)) hL
        convert this using 1
        simp only [Finset.prod_pair hab, smul_eq_mul]
        ring
    rw [Cube.d_apply]
    have hbt : b ∈ t.1 := by rw [hab']; simp
    have key : ∀ i : t.1, Cube.res (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)
        (Finset.erase_subset i.1 t.1) (x (Cube.eraseIdx t i)) =
        Cube.res (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)
        (Finset.erase_subset b t.1) (x (Cube.eraseIdx t ⟨b, hbt⟩)) := by
      intro i
      obtain ⟨j, hj, e⟩ := hres (Cube.eraseIdx t i) t.1 (Finset.erase_subset i.1 t.1)
      obtain ⟨j', hj', e'⟩ := hres (Cube.eraseIdx t ⟨b, hbt⟩) t.1 (Finset.erase_subset b t.1)
      exact Subtype.ext (e.trans (((hv j (Finset.mem_of_mem_erase hj)).trans
        (hv j' (Finset.mem_of_mem_erase hj')).symm).trans e'.symm))
    rw [Finset.sum_congr rfl fun i _ => by rw [key i], ← Finset.sum_smul,
      Finset.sum_coe_sort t.1 (cubeSign t.1), sum_cubeSign_pair t.2, zero_smul]
    rfl

  obtain ⟨m, hm⟩ := hb.2 ((cechHomologyZeroIso
    (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)).inv.hom ⟨x, hx⟩)
  obtain ⟨G, hG, hGm⟩ := m.2
  refine ⟨G, mem_polyGrading_natCast.1 hG, fun i => ?_⟩
  have e := cechHomologyZeroIso_grAug_local (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) (d : ℤ) m
    ⟨{i}, Finset.card_singleton i⟩
  have e2 : (cechHomologyZeroIso
      (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)).hom.hom
      ((cechHomologyZeroIso
      (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)).inv.hom ⟨x, hx⟩) =
      ⟨x, hx⟩ :=
    congr(($((cechHomologyZeroIso
      (grCube (Fin (n + 1)) (grQuot (polyGrading (Fin (n + 1)) A) J) d)).inv_hom_id)).hom ⟨x, hx⟩)
  rw [hm, e2] at e
  have e3 : x ⟨{i}, Finset.card_singleton i⟩ = y i := Cube.termOneEquiv_apply _ y i
  have e4 := congrArg Subtype.val (e3.symm.trans e)
  erw [coe_toHomLoc] at e4
  rw [← hGm, awayFrac_eq_iff] at e4
  obtain ⟨l, hl⟩ := e4
  refine ⟨l, ?_⟩
  simp only [xProd, Finset.prod_singleton, LinearMap.coe_restrictScalars, Submodule.mkQ_apply] at hl
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul (p := J) (X i ^ (l + N)),
    Submodule.Quotient.eq] at hl
  convert hl using 1
  simp only [smul_eq_mul]
  ring

end GlobalTheory
