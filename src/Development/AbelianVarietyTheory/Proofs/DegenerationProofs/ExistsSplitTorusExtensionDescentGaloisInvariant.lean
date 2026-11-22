module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.NotIsGaloisCoverTrivial
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusExtensionDescends
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem exists_splitExt_of_galois_invariant :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (G₀ B₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] [GrpObj B₀], IsAbelianScheme B₀ → ∀ (G B : Over (Sp K)) [GrpObj G] [GrpObj B] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (φG : G.left ⟶ G₀.left) (φ : B.left ⟶ B₀.left), IsGrpPullback G G₀ (spMap (algebraMap k K)) φG → IsGrpPullback B B₀ (spMap (algebraMap k K)) φ → ∀ (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G), IsMonHom q → Flat q.left → Surjective q.left → QuasiCompact q.left → IsMonHom i → IsPullback i (toUnit _) q (η[B] : 𝟙_ _ ⟶ B) → (∀ (τ : K ≃ₐ[k] K) (s : G.left ⟶ G.left), s ≫ φG = φG → s ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) → s ≫ q.left ≫ φ = q.left ≫ φ ∧ GlobalTheory.SplitTorus.bcMap (spMap (τ : K →+* K)) X ≫ i.left = i.left ≫ s) → ∃ S : SplitExt (Sp k), S.IsGt G₀ := by
  intro k K _ _ _ _ _ G₀ B₀ _ _ _ hB₀ G B _ _ X _ _ _ φG φ hG hB q i hq hfl hsu hqc hi H hinv
  have spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
      spMap (g.comp f) = spMap g ≫ spMap f := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl

  have spMap_surjective' {A B : Type} [CommRing A] [CommRing B] (y : Sp B ⟶ Sp A) :
      ∃ f : A →+* B, spMap f = y :=
    ⟨(Spec.preimage y).hom, by simp [spMap]⟩

  have spMap_inj_lemma_3 {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
      f = g := by
    have h' := Spec.map_injective h
    exact congrArg CommRingCat.Hom.hom h'

  have hc : GlobalTheory.ZM.IsGaloisCover (K ≃ₐ[k] K) (fun σ => spMap (σ : K →+* K)) (spMap (algebraMap k K)) := by
    refine
      { finite := inferInstance
        one := ?_
        mul := ?_
        inv := ?_
        fin := ?_
        etale := ?_
        onto := ?_
        fibre := ?_ }
    · show Spec.map _ = _
      convert Spec.map_id (CommRingCat.of K)
      rfl
    · intro a c
      show spMap (((a * c : K ≃ₐ[k] K) : K →+* K)) = _
      rw [← spMap_comp_moduli_spaces]
      rfl
    · intro a
      rw [← spMap_comp_moduli_spaces]
      congr 1
      ext r
      exact a.commutes r
    · show IsFinite (Spec.map _)
      rw [IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr inferInstance
    · show Etale (Spec.map _)
      rw [HasRingHomProperty.Spec_iff (P := @Etale)]
      show (algebraMap k K).Etale
      rw [RingHom.etale_algebraMap]
      exact ⟨Algebra.FormallyEtale.of_isSeparable k K, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
    · exact ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
    · intro k' _ _ y y' h
      obtain ⟨f, rfl⟩ := spMap_surjective' y
      obtain ⟨f', rfl⟩ := spMap_surjective' y'
      rw [← spMap_comp_moduli_spaces, ← spMap_comp_moduli_spaces] at h
      have hfa := spMap_inj_lemma_3 h
      let _ : Algebra k k' := (f.comp (algebraMap k K)).toAlgebra
      let φ : K →ₐ[k] k' := { f with commutes' := fun _ => rfl }
      let φ' : K →ₐ[k] k' :=
        { f' with commutes' := fun r => (RingHom.congr_fun hfa r).symm }
      let Φ : (K ≃ₐ[k] K) → (K →ₐ[k] k') := fun a => φ.comp a.toAlgHom
      have hinj : Function.Injective Φ := by
        intro a b hab
        ext x
        exact f.injective (AlgHom.congr_fun hab x)
      have hcard : Nat.card (K →ₐ[k] k') ≤ Nat.card (K ≃ₐ[k] K) := by
        rw [IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, AlgHom.card]
      obtain ⟨a, ha⟩ := (hinj.bijective_of_nat_card_le hcard).2 φ'
      refine ⟨a, ?_, fun b hb => ?_⟩
      · show spMap f ≫ spMap (a : K →+* K) = spMap f'
        rw [← spMap_comp_moduli_spaces]
        congr 1
        ext x
        exact AlgHom.congr_fun ha x
      · have hb' : f.comp (b : K →+* K) = f' := by
          have hb0 : spMap f ≫ spMap (b : K →+* K) = spMap f' := hb
          rw [← spMap_comp_moduli_spaces] at hb0
          exact spMap_inj_lemma_3 hb0
        apply hinj
        ext x
        exact (RingHom.congr_fun hb' x).trans (AlgHom.congr_fun ha x).symm
  have coverPull {A B A' B' : Scheme} {p : A ⟶ B} {p' : A' ⟶ B'}
      {Γ : Type} [Group Γ] {ρ : Γ → (A ⟶ A)} {ρ' : Γ → (A' ⟶ A')}
      {u : A' ⟶ A} {v : B' ⟶ B} (h : GlobalTheory.ZM.IsGaloisCover Γ ρ p)
      (hp : IsPullback u p' p v) (hu : ∀ a, ρ' a ≫ u = u ≫ ρ a)
      (hin : ∀ a, ρ' a ≫ p' = p') : GlobalTheory.ZM.IsGaloisCover Γ ρ' p' :=
    ((GlobalTheory.ZM.galoisCover_descent A B p Γ ρ h).2.2 A' B' p' ρ' u v hu hp.w).2 hp hin
  have coverDesc {A B : Scheme} {p : A ⟶ B} {Γ : Type} [Group Γ]
      {ρ : Γ → (A ⟶ A)} (h : GlobalTheory.ZM.IsGaloisCover Γ ρ p)
      {Z : Scheme} (f : A ⟶ Z) (hf : ∀ a, ρ a ≫ f = f) :
      ∃! f' : B ⟶ Z, p ≫ f' = f :=
    (GlobalTheory.ZM.galoisCover_descent A B p Γ ρ h).1 Z f hf
  let s : (K ≃ₐ[k] K) → (G.left ⟶ G.left) := fun τ =>
    hG.1.lift φG (G.hom ≫ spMap (τ : K →+* K)) (by rw [Category.assoc, hc.inv, hG.1.w])
  have hs₁ : ∀ τ, s τ ≫ φG = φG := fun τ => hG.1.lift_fst _ _ _
  have hs₂ : ∀ τ, s τ ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) := fun τ => hG.1.lift_snd _ _ _
  have hcG := coverPull hc (ρ' := s) hG.1.flip hs₂ hs₁
  have bcFst {S S' : Scheme} (f : S' ⟶ S) :
      SplitTorus.bcMap f X ≫ Rosenlicht.torusFst S X = Rosenlicht.torusFst S' X :=
    pullback.lift_fst _ _ _
  have hT := SplitTorus.isPullback_bcMap (spMap (algebraMap k K)) X
  have hcT := coverPull hc
    (ρ' := fun τ : K ≃ₐ[k] K => SplitTorus.bcMap (spMap (τ : K →+* K)) X) hT.flip
    (fun τ => SplitTorus.bcMap_hom _ X) (fun τ => pullback.hom_ext
      (by
        have e := bcFst (spMap (algebraMap k K))
        exact (Category.assoc _ _ _).trans ((congrArg _ e).trans
          ((bcFst _).trans e.symm)))
      (by
        have e := SplitTorus.bcMap_hom (spMap (algebraMap k K)) X
        refine (Category.assoc _ _ _).trans ((congrArg _ e).trans (Eq.trans ?_ e.symm))
        rw [SplitTorus.bcMap_hom_assoc, hc.inv]))
  obtain ⟨q', hq', -⟩ := coverDesc hcG (q.left ≫ φ) fun τ => (hinv τ _ (hs₁ τ) (hs₂ τ)).1
  obtain ⟨i', hi', -⟩ := coverDesc hcT (i.left ≫ φG) fun τ => by
    rw [← Category.assoc, (hinv τ _ (hs₁ τ) (hs₂ τ)).2, Category.assoc, hs₁]
  have wq : q' ≫ B₀.hom = G₀.hom :=
    (coverDesc hcG (φG ≫ G₀.hom) fun τ => by rw [← Category.assoc, hs₁]).unique
      (by rw [← Category.assoc, hq', Category.assoc, hB.1.w, ← Category.assoc, Over.w, hG.1.w]) rfl
  have wi : i' ≫ G₀.hom = (splitTorus (Sp k) X).hom :=
    (coverDesc hcT (SplitTorus.bcMap (spMap (algebraMap k K)) X ≫ (splitTorus (Sp k) X).hom)
      fun τ => by rw [← Category.assoc, hcT.inv]).unique
      (by rw [← Category.assoc, hi', Category.assoc, hG.1.w, ← Category.assoc, Over.w, hT.w]) rfl
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := splitTorus_extension_descends k K (algebraMap k K) G B G₀ B₀ X
    φG φ hG hB q i (Over.homMk q' wq) (Over.homMk i' wi) hq' hi' hq hfl hsu hqc hi H
  obtain ⟨O, a, b, c, h⟩ := exists_gtDatum_of_splitTorus_extension (Sp k) X G₀ B₀ hB₀ _ _
    h₁ h₅ h₂ h₃ h₄ h₆
  obtain ⟨d, -⟩ := h hB₀
  exact ⟨_, ⟨d⟩⟩

end GlobalTheory

