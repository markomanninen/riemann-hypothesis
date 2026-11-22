module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSimplicialCochainRepresentingClassAcyclicL
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_simplicialCochain_representing_class_acyclicLevels :
    ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ),
      (∀ k m : ℕ, 0 < m → k + m = n →
        ∀ y : H R (disc.obj (E.obj (op (SimplexCategory.mk k)))) F m, y = 0) →
      ∀ x : H R E F n, ∃ s : (free R).obj (E.obj (op (SimplexCategory.mk n))) ⟶ F,
        GlobalTheory.EtC.cobd (R := R) s = 0 ∧ GlobalTheory.EtC.IsCls (R := R) s x := by
  intro R _ F E n hyp x
  obtain ⟨z, rfl, hv⟩ := GlobalTheory.EtC.LeraySurj.reduce F E n hyp x n le_rfl
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, -⟩ :=
    GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  have hcl : z.1.v (-(n : ℤ)) 0 (by omega) ≫ (res R F).d 0 1 = 0 := by
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-(n : ℤ)) 1 (by omega)
    rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ 0 (-(n : ℤ) + 1) (by omega) rfl,
      hv (-(n : ℤ) + 1) _ _ (by omega)] at h
    simpa using h
  obtain ⟨u, hu⟩ := hex.lift' ((chainsXIso R E n).inv ≫ z.1.v (-(n : ℤ)) 0 (by omega))
    (by change _ ≫ (res R F).d 0 1 = 0; rw [Category.assoc, hcl, Limits.comp_zero])
  change u ≫ resι R F = _ at hu
  have hz : z.1.v (-(n : ℤ)) 0 (by omega) = (chainsXIso R E n).hom ≫ u ≫ resι R F := by
    rw [hu, Iso.hom_inv_id_assoc]
  have hcobd : GlobalTheory.EtC.cobd (R := R) u =
      (chainsXIso R E (n + 1)).inv ≫ ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫
        (chainsXIso R E n).hom ≫ u := by
    rw [GlobalTheory.EtC.LeraySurj.chains_d_eq]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.sum_comp, Preadditive.zsmul_comp]
    rfl
  refine ⟨u, ?_, z, rfl, ?_⟩
  · rw [hcobd]
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-((n + 1 : ℕ) : ℤ)) 0 (by omega)
    rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ (-1) (-(n : ℤ)) (by omega) (by omega), hz,
      (hneg (-1) (by omega)).eq_of_tgt (z.1.v _ (-1) _) 0] at h
    simp only [Limits.zero_comp, zero_add, Cochain.zero_v] at h
    have h' := (smul_eq_zero_iff_eq _).1 h
    have h'' : (((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ (chainsXIso R E n).hom ≫ u) ≫
        resι R F = 0 ≫ resι R F := by
      simpa [Category.assoc] using h'
    rw [cancel_mono] at h''
    rw [h'', Limits.comp_zero]
  · refine Cochain.ext _ _ (fun p q hpq => ?_)
    rcases lt_trichotomy p (-(n : ℤ)) with h | h | h
    · exact (hneg q (by omega)).eq_of_tgt _ _
    · subst h
      obtain rfl : q = 0 := by omega
      rw [Cochain.single_v, hz]
    · rw [hv p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
