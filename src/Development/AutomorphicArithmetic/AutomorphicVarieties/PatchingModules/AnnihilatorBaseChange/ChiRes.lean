module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.HomTwo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem chi_diag {n : ℕ} {k G : Type} [CommRing k] [Group G] (χ : Fin n → G →* kˣ) (g : G) :
    (GDet.ofRep (diagRep χ)).chi (MonoidAlgebra.single g 1) =
      ∏ i, (Polynomial.X - Polynomial.C (χ i g : k)) := by
  change (GDet.repAlg (diagRep χ) (Polynomial k) _).det = _
  rw [← Matrix.det_diagonal]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, diagRep, Matrix.one_apply, Matrix.diagonal_apply, h]

theorem UpperTheory.V.Pa.Core.chiRes :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid F O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (g : F.G₀) (ut : Fin n → O), (∀ i, residue O (ut i) = r.chib i g) → (u.D.chi (MonoidAlgebra.single g 1)).Monic ∧ (u.D.chi (MonoidAlgebra.single g 1)).natDegree = n ∧ (u.D.chi (MonoidAlgebra.single g 1)).map (residue B) = ∏ i, (Polynomial.X - Polynomial.C (residue B (algebraMap O B (ut i)))) := by
  intro l _ F n O _ _ _ r B _ _ _ u g ut hut
  have hm : (u.D.chi (MonoidAlgebra.single g 1)).Monic := by
    have hchi : u.D.toDet.chi (MonoidAlgebra.single g 1) = u.D.chi (MonoidAlgebra.single g 1) := by
      change u.D.D (Polynomial B) (ofT B F.G₀ (Polynomial B)
        (Polynomial.X ⊗ₜ 1 - 1 ⊗ₜ MonoidAlgebra.single g 1)) = _
      congr 1
      rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul,
        MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rfl
    rw [← hchi]
    exact (UpperTheory.V.CA.d_chi _ _).2.2.2.2.1
  have h1 : (u.D.chi (MonoidAlgebra.single g 1)).map (res O B : B →+* ResidueField O) =
      ∏ i, (Polynomial.X - Polynomial.C (residue O (ut i))) := by
    have hchi : (u.D.map (res O B : B →+* ResidueField O)).chi
        (MonoidAlgebra.mapRingHom F.G₀ (res O B : B →+* ResidueField O) (MonoidAlgebra.single g 1)) =
        (u.D.chi (MonoidAlgebra.single g 1)).map (res O B) := by
      let f : B →+* ResidueField O := res O B
      letI : Algebra B (Polynomial (ResidueField O)) := ((algebraMap _ _).comp f).toAlgebra
      let φ : Polynomial B →ₐ[B] Polynomial (ResidueField O) :=
        { Polynomial.mapRingHom f with
          commutes' := fun a => by
            change Polynomial.map f (Polynomial.C a) = Polynomial.C (f a)
            exact Polynomial.map_C f }
      have h := u.D.nat (Polynomial B) (Polynomial (ResidueField O)) φ
        (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom F.G₀ Polynomial.C (MonoidAlgebra.single g 1))
      refine Eq.trans ?_ h
      change u.D.D (Polynomial (ResidueField O)) _ = u.D.D (Polynomial (ResidueField O)) _
      congr 1
      have hφ : (φ : Polynomial B →+* Polynomial (ResidueField O)) = Polynomial.mapRingHom f := rfl
      rw [hφ]
      ext x : 2
      simp
    rw [← hchi, u.red, MonoidAlgebra.mapRingHom_single, map_one, Resid.Dbar,
      chi_diag]
    simp only [hut]
  have hc : (ResidueField.map (algebraMap O B)).comp (res O B : B →+* ResidueField O) = residue B := by
    ext x
    exact (RingEquiv.ofBijective _ (resMap_bijective O B)).apply_symm_apply (residue B x)
  have h2 : (u.D.chi (MonoidAlgebra.single g 1)).map (residue B) =
      ∏ i, (Polynomial.X - Polynomial.C (residue B (algebraMap O B (ut i)))) := by
    conv_lhs => rw [← hc, ← Polynomial.map_map, h1]
    simp [Polynomial.map_prod, ResidueField.map_residue]
  refine ⟨hm, ?_, h2⟩
  rw [← hm.natDegree_map (residue B), h2, Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
  simp
