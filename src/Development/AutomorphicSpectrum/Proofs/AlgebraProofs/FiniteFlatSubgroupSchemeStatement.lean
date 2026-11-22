module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatSubgroupScheme
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR
open GlobalTheory.CompanionTheory.Ar.GR.SubGrp (exists_eq_spMap exists_sp_iso exists_grpObj_of_mono) in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_subgroup_scheme :
    ∀ (R : Type) [CommRing R] (A : Over (Spec (CommRingCat.of R))) [GrpObj A]
      (B : Type) [CommRing B] [Algebra R B] (h : sp (R₀ := R) B ⟶ A),
      IsFinFlatSub A B h → ∃ _ : GrpObj (sp (R₀ := R) B), IsMonHom h ∧ Mono h := by
  intro R _ A _ B _ _ h H
  have hmono : Mono h := by
    constructor
    intro T a b hab
    apply Over.OverMorphism.ext
    refine T.left.affineCover.hom_ext _ _ fun k => ?_
    let T' : Over (Spec (CommRingCat.of R)) := Over.mk (T.left.affineCover.f k ≫ T.hom)
    let j : T' ⟶ T := Over.homMk (T.left.affineCover.f k) rfl
    have : IsAffine T'.left := inferInstanceAs (IsAffine (T.left.affineCover.X k))
    obtain ⟨S, _, _, i, _⟩ := exists_sp_iso T'
    obtain ⟨φ, hφ⟩ := exists_eq_spMap (i ≫ j ≫ a)
    obtain ⟨ψ, hψ⟩ := exists_eq_spMap (i ≫ j ≫ b)
    have hφψ := H.mono S φ ψ (by simp only [← hφ, ← hψ, Category.assoc, hab])
    have hj : j ≫ a = j ≫ b := by rw [← cancel_epi i, hφ, hψ, hφψ]
    exact congrArg (·.left) hj
  have hmul : ∃ m : sp (R₀ := R) B ⊗ sp (R₀ := R) B ⟶ sp (R₀ := R) B,
      m ≫ h = (fst _ _ ≫ h) * (snd _ _ ≫ h) := by
    have : IsAffine (sp (R₀ := R) B).left := inferInstanceAs (IsAffine (Spec _))
    have : IsAffine (sp (R₀ := R) B ⊗ sp (R₀ := R) B).left :=
      Scheme.Pullback.isAffine_of_isAffine_isAffine_isAffine
        (sp (R₀ := R) B).hom (sp (R₀ := R) B).hom
    obtain ⟨S, _, _, j, _⟩ := exists_sp_iso (sp (R₀ := R) B ⊗ sp (R₀ := R) B)
    obtain ⟨φ, hφ⟩ := exists_eq_spMap (j ≫ fst _ _)
    obtain ⟨ψ, hψ⟩ := exists_eq_spMap (j ≫ snd _ _)
    obtain ⟨χ, hχ⟩ := H.mul S φ ψ
    refine ⟨inv j ≫ spMap χ, ?_⟩
    rw [Category.assoc, hχ, ← hφ, ← hψ, MonObj.comp_mul, Category.assoc, Category.assoc,
      IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]
  have hone : ∃ e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ sp (R₀ := R) B, e ≫ h = 1 := by
    have : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
      inferInstanceAs (IsAffine (Spec _))
    obtain ⟨S, _, _, j, _⟩ := exists_sp_iso (𝟙_ (Over (Spec (CommRingCat.of R))))
    obtain ⟨χ, hχ⟩ := H.one S
    exact ⟨inv j ≫ spMap χ, by rw [Category.assoc, hχ, MonObj.comp_one]⟩
  obtain ⟨i, hi⟩ := H.inv B (AlgHom.id R B)
  have hid : spMap (AlgHom.id R B) = 𝟙 (sp (R₀ := R) B) := by
    apply Over.OverMorphism.ext
    rw [ReciprocityTheory.ChartRestriction.G.Chart.spMap_left, Over.id_left]
    exact Spec.map_id _
  rw [hid, Category.id_comp] at hi
  obtain ⟨m, hm⟩ := hmul
  obtain ⟨e, he⟩ := hone
  obtain ⟨G, hG⟩ := exists_grpObj_of_mono h m e (spMap i) hm he hi
  exact ⟨G, hG, hmono⟩
