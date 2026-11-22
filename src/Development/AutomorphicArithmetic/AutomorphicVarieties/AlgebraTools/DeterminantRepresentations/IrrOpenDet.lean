module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MatIrrIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MapApi

@[expose] public section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.irrOpenDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (H : Subgroup G),
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (p : PrimeSpectrum A),
        p.asIdeal = RingHom.ker φ → D.map φ = GDet.ofRep ρ → (p ∈ U ↔ U3.MatIrr H ρ) := by
  intro n A G _ _ D H
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨Set.univ, isOpen_univ, ?_⟩
    intro K _ _ φ ρ p _ _
    rw [UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Set.mem_univ _⟩
  · obtain ⟨U, hU, h⟩ := UpperTheory.V.AlgebraTools.Det.irrOpen (ι := Fin n)
      (fun h : H => D.tr (MonoidAlgebra.single (h : G) 1))
    refine ⟨U, hU, ?_⟩
    intro K _ _ φ ρ p hp hD
    rw [UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ]
    refine h K φ (ρ.comp H.subtype) p hp ?_
    intro g
    have hmap : (D.map φ).chi (MonoidAlgebra.single (g : G) 1) =
        (D.chi (MonoidAlgebra.single (g : G) 1)).map φ := by
      let : Algebra A K[X] := ((algebraMap K K[X]).comp φ).toAlgebra
      let f : A[X] →ₐ[A] K[X] :=
        { Polynomial.mapRingHom φ with
          commutes' := fun a => by
            change Polynomial.mapRingHom φ (algebraMap A A[X] a) = algebraMap K K[X] (φ a)
            simp [Polynomial.algebraMap_eq] }
      change D.D K[X] (MonoidAlgebra.single 1 X -
        MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single (g : G) 1)) = f (D.chi _)
      rw [GDet.chi, ← D.nat A[X] K[X] f]
      congr 1
      simp [f]
    have hrep : (GDet.ofRep ρ).chi (MonoidAlgebra.single (g : G) 1) = (ρ g).charpoly := by
      change (GDet.repAlg ρ K[X] (MonoidAlgebra.single 1 X -
        MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single (g : G) 1))).det = _
      rw [map_sub, MonoidAlgebra.mapRingHom_single, map_one, Matrix.charpoly]
      simp only [GDet.repAlg, MonoidAlgebra.lift_single, MonoidHom.comp_apply,
        map_one, one_smul, Polynomial.algebraMap_eq]
      rw [Matrix.charmatrix, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
      rfl
    rw [hD, hrep] at hmap
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    change (ρ g).trace = φ (D.lam 1 _)
    rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, hmap, Polynomial.coeff_map]
    simp [GDet.lam]
