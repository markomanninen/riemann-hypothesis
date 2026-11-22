module

public import Mathlib
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
public import Development.AutomorphicArithmetic.CommutativeAlgebra.SupportDoubleComplexTotalRepresentsVanishingCoch
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

namespace UpperTheory.ConstantCochains

variable {R : Type} [CommRing R] {E : Spc} {K : Cx R}

private theorem map_id' {p : ℕ} {U : Scheme.{0}} (z : Sx E p U) : Sx.map (𝟙 E) z = z := rfl

private def cst {U : Scheme.{0}} {a b : ℤ} (e : a = b) (v : Sec (K.X a) U) : Sec (K.X b) U := e ▸ v

private theorem res_cst {V U : Scheme.{0}} (g : V ⟶ U) {a b : ℤ} (e : a = b) (v : Sec (K.X a) U) :
    Sec.res g (cst e v) = cst e (Sec.res g v) := by
  subst e; rfl

private theorem cst_fam (x : (famDC (Sub.bot E) K 0).Tot) (p : ℕ) (U : Scheme.{0}) (z : Sx E p U)
    {s t : ℤ} (e : t = s) (e' : t + 0 = s + 0) :
    (show Fam (Sub.bot E) p (K.X (s + 0)) from x p s).1 U z =
      cst e' ((show Fam (Sub.bot E) p (K.X (t + 0)) from x p t).1 U z) := by
  subst e; rfl

private theorem exists_cochain (n : ℤ) (x : (famDC (Sub.bot E) K 0).Tot) :
    ∃ γ : Cochain ((chains R).obj E) K n, Comp (𝟙 E) γ x := by
  let a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (K.X s) U :=
    fun p s _ U z => cst (add_zero s) ((x p s).1 U z)
  have ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (z : Sx E p U),
      Sec.res g (a p s h U z) = a p s h V (z.res g) := by
    intro p s h V U g z
    exact (res_cst g _ _).trans (congrArg (cst (add_zero s)) ((x p s).2.1 V U g z))
  have components : ∀ (i j : ℤ) (hij : i + n = j), ∃ φ : ((chains R).obj E).X i ⟶ K.X j,
      ∀ (p : ℕ) (hp : i = -(p : ℤ)) U z,
        Sec.map ((chainsXIso R E p).inv ≫ eqToHom (congrArg ((chains R).obj E).X hp.symm) ≫ φ)
          (freeGen R _ U z) = a p j (hp ▸ hij) U z := by
    intro i j hij
    by_cases hi : i ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (a k j hij) (ha k j hij)
      refine ⟨(chainsXIso R E k).hom ≫ φ, fun p hp U z => ?_⟩
      obtain rfl : k = p := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U z
    · exact ⟨0, fun p hp => by omega⟩
  choose φ hφ using components
  let γ : Cochain ((chains R).obj E) K n := Cochain.mk φ
  have hγ : ∀ p s h U z, ev γ p s h U z = a p s h U z := by
    intro p s h U z
    have he := hφ _ _ h p rfl U z
    rw [eqToHom_refl, Category.id_comp] at he
    exact he
  refine ⟨γ, ?_⟩
  intro p s h U z
  rw [map_id', hγ]
  exact cst_fam x p U z (add_zero s) (add_zero (s + 0))

private theorem eq_zero_of_comp {N : ℤ} (γ : Cochain ((chains R).obj E) K N)
    (h : Comp (𝟙 E) γ (0 : (famDC (Sub.bot E) K 0).Tot)) : γ = 0 := by
  have hext : ∀ α β : Cochain ((chains R).obj E) K N,
      (∀ p s h U z, ev α p s h U z = ev β p s h U z) → α = β := by
    intro α β H
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = -(k : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R E k).inv]
      exact CupSpec.free_ext _ _ (fun U z => H k s hs U z)
    · exact (CupSpec.isZero_chains E p (by omega)).eq_of_src _ _
  apply hext
  intro p s hs U z
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 0 := ⟨s, (add_zero s).symm⟩
  have h1 := h p t hs U z
  rw [map_id'] at h1
  rw [← h1]
  simp [ev]
  rfl

private theorem eq_of_comp {N : ℤ} (γ γ' : Cochain ((chains R).obj E) K N)
    (x : (famDC (Sub.bot E) K 0).Tot) (h : Comp (𝟙 E) γ x) (h' : Comp (𝟙 E) γ' x) : γ = γ' := by
  have h2 := (UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 N N (add_zero N)).2.2.2.1 γ γ' x x h h'
  rw [sub_self] at h2
  exact sub_eq_zero.1 (eq_zero_of_comp _ h2)

end UpperTheory.ConstantCochains

open UpperTheory.ConstantCochains in
theorem UpperTheory.supportDoubleComplex_bot_totalModel :
    ∀ (R : Type) [CommRing R] (E : Spc) (K : Cx R) (n : ℤ), TModel (famDC (Sub.bot E) K 0) n (HRel (E := E) (K := K) (n := n)) := by
  intro R _ E K n
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have Ik := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 k k (add_zero k)
  have I1 := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 (k + 1) (k + 1) (add_zero _)
  have I2 := UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain R (𝟙 E) (Sub.bot E) K 0 (k + 1 + 1) (k + 1 + 1) (add_zero _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hD
    obtain ⟨γ, hγ⟩ := exists_cochain (k + 1) x
    have h1 := I1.2.2.1 γ x hγ
    rw [hD] at h1
    have h0 := eq_zero_of_comp _ h1
    exact ⟨CohomologyClass.mk (Cocycle.mk γ _ rfl h0), Cocycle.mk γ _ rfl h0, rfl, hγ⟩
  · intro c
    obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
    obtain ⟨x, hx, hc⟩ := I1.1 γ (fun _ _ _ _ _ hm => False.elim hm)
    refine ⟨x, hx, ?_, γ, rfl, hc⟩
    have h1 := I1.2.2.1 γ x hc
    rw [Cocycle.δ_eq_zero] at h1
    have c00 : Comp (𝟙 E) (0 : Cochain ((chains R).obj E) K (k + 1 + 1))
        (0 : (famDC (Sub.bot E) K 0).Tot) := by
      intro p s h U z
      simp [ev]
      rfl
    exact I2.2.1 0 _ 0 (I1.2.2.2.2 x hx) (fun _ _ _ => rfl) h1 c00
  · rintro x c x' c' ⟨γ, rfl, hγ⟩ ⟨γ', rfl, hγ'⟩
    exact ⟨γ - γ', CohomologyClass.mk_sub _ _, I1.2.2.2.1 _ _ _ _ hγ hγ'⟩
  · rintro x c hx ⟨γ, rfl, hγ⟩
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff γ k rfl, add_sub_cancel_right]
    constructor
    · rintro ⟨β, hβ⟩
      obtain ⟨y, hy, hyβ⟩ := Ik.1 β (fun _ _ _ _ _ hm => False.elim hm)
      refine ⟨y, hy, ?_⟩
      have h1 := Ik.2.2.1 β y hyβ
      rw [hβ] at h1
      exact I1.2.1 _ _ _ (Ik.2.2.2.2 y hy) hx h1 hγ
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨β, hβ⟩ := exists_cochain k y
      exact ⟨β, eq_of_comp _ _ _ (Ik.2.2.1 β y hβ) hγ⟩
