module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext

@[expose] public section

open Polynomial TensorProduct UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.extDense :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [T2Space A] [TopologicalSpace G] (D D' : GDet n A G) (S : Set G), Dense S →
    (∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1)) →
    (∀ i ≤ n, Continuous fun g : G => D'.lam i (MonoidAlgebra.single g 1)) →
    (∀ g ∈ S, D.chi (MonoidAlgebra.single g 1) = D'.chi (MonoidAlgebra.single g 1)) → D = D' := by
  intro n A G _ _ _ _ _ D D' S hS hc hc' hchi
  have hlam (g : G) (i : ℕ) (hi : i ≤ n) :
      D.lam i (MonoidAlgebra.single g 1) = D'.lam i (MonoidAlgebra.single g 1) := by
    have h := Continuous.ext_on hS (hc i hi) (hc' i hi) (fun x hx => by
      show (-1) ^ i * (D.chi _).coeff (n - i) = (-1) ^ i * (D'.chi _).coeff (n - i)
      rw [hchi x hx])
    exact congrFun h g
  have htoDet (F : GDet n A G) (y : MonoidAlgebra A G) (i : ℕ) :
      F.toDet.lam i y = F.lam i y := by
    have h : F.toDet.chi y = F.chi y := by
      change F.D A[X] (ofT A G A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)) =
        F.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
      congr 1
      rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul, MonoidAlgebra.one_def,
        MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rfl
    unfold Det.lam GDet.lam
    rw [h]
  have hdet : D.toDet = D'.toDet := by
    refine UpperTheory.V.CA.d_ext D.toDet D'.toDet (MonoidHom.mrange (MonoidAlgebra.of A G)) ?_ ?_
    · rw [Submodule.eq_top_iff']
      intro x
      induction x using MonoidAlgebra.induction_linear with
      | zero => exact zero_mem _
      | add a b ha hb => exact add_mem ha hb
      | single g r =>
        have h : MonoidAlgebra.single g r = r • MonoidAlgebra.single g (1 : A) := by simp
        rw [h]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
    · rintro x ⟨g, rfl⟩ i _ hi
      rw [htoDet, htoDet]
      exact hlam g i hi
  rw [← GDet.ofDet_toDet D, hdet, GDet.ofDet_toDet]
