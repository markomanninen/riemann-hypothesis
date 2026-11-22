module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjHyp

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace ReciprocityTheory.AnForm.R

namespace FinalTheorems

def GFLogStC : Prop :=
  ∀ (X : Scheme.{0}) [IsNoetherian X], (∃ f : X ⟶ Spec (CommRingCat.of ℂ), LocallyOfFiniteType f) →
    QE X → IsReduced X → FFinRes X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ → LogResStC X B

theorem gfLogStC_of_CR (h : GFLogStCR.{0}) : GFLogStC := fun X _ _ a b c B d e => h X a b c B d e

end FinalTheorems

def ProjLogResC : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (hP : IsMultiHomogIdeal P), IsMultiHomogIdeal D → P.IsRadical →
    (∀ (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval y h = 0) →
      ¬ IsRegularLocalRing (chartLocRing P p y) → ∀ f ∈ D, eval y f = 0) →
    (∀ q ∈ P.minimalPrimes, IsRelevant q → ¬ D ≤ q) → FinalTheorems.LogResStC (projX P hP) (projB P D hP)

theorem projLogResC_of_C (hC : FinalTheorems.GFLogStC) (hQ : FinalTheorems.FinTypeQE) : ProjLogResC :=
  fun _ _ _ _ _ P _ hP hD hrad hsing hmin => by
    have hft : LocallyOfFiniteType (toSpecC hP) := by
      classical
      let := segreGraded hP
      let A := MvPolynomial ((k : _) → _) ℂ ⧸ segreIdeal P
      have : Algebra.FiniteType ℂ A :=
        Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ (segreIdeal P))
          (Ideal.Quotient.mkₐ_surjective ℂ _)
      have : IsScalarTower ℂ (segreGrading P 0) A :=
        IsScalarTower.of_algebraMap_eq fun c => by
          rw [← SetLike.GradeZero.coe_algebraMap (segreGrading P) c]
          rfl
      have : Algebra.FiniteType (segreGrading P 0) A :=
        Algebra.FiniteType.of_restrictScalars_finiteType ℂ (segreGrading P 0) A
      have hsurj : Function.Surjective (algebraMap ℂ (segreGrading P 0)) := by
        rintro ⟨x, hx⟩
        obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.1 hx
        have hq' : q.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 q).1 hq
        refine ⟨q.coeff 0, ?_⟩
        apply Subtype.ext
        rw [SetLike.GradeZero.coe_algebraMap]
        by_cases h0 : q = 0
        · subst q
          simp
        · have hCq : q = C (q.coeff 0) := totalDegree_eq_zero_iff_eq_C.1 (hq'.totalDegree h0)
          show _ = (Ideal.Quotient.mkₐ ℂ (segreIdeal P)) q
          nth_rewrite 2 [hCq]
          exact ((Ideal.Quotient.mkₐ ℂ _).commutes (q.coeff 0)).symm
      have hbase : LocallyOfFiniteType
          (Spec.map (CommRingCat.ofHom (algebraMap ℂ (segreGrading P 0)))) := by
        rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
        exact RingHom.FiniteType.of_surjective _ hsurj
      have hproj : LocallyOfFiniteType (Proj.toSpecZero (segreGrading P)) := inferInstance
      exact @locallyOfFiniteType_comp _ _ _ (Proj.toSpecZero (segreGrading P)) _ hproj hbase
    exact hC (projX P hP) ⟨toSpecC hP, hft⟩
      (qe_projX hP hQ) (isReduced_projX hP hrad) (fFinRes_projX hP) _
      (sing_subset_projB hP hD hQ hsing) (interior_projB hP hD hmin)

theorem projLogResC_of_CR (hC : FinalTheorems.GFLogStCR.{0}) (hQ : FinalTheorems.FinTypeQE) : ProjLogResC :=
  projLogResC_of_C (FinalTheorems.gfLogStC_of_CR hC) hQ

end ReciprocityTheory.AnForm.R
