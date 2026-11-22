module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GroupDetExistsSemisimpleRepresentation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrOpenDet

@[expose] public section

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

theorem UpperTheory.V.CA.stable_field :
    ∀ {n : ℕ} {A G κ κ' : Type} [CommRing A] [Group G] [Field κ] [IsAlgClosed κ] [Field κ'] [IsAlgClosed κ'] (D : GDet n A G) (f : A →+* κ) (f' : A →+* κ'), RingHom.ker f = RingHom.ker f' → (∃ ρ : G →* Matrix (Fin n) (Fin n) κ, UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f = GDet.ofRep ρ) → ∃ ρ : G →* Matrix (Fin n) (Fin n) κ', UpperTheory.V.U3.MatIrr ⊤ ρ ∧ D.map f' = GDet.ofRep ρ := by
  intro n A G κ κ' _ _ _ _ _ _ D f f' hker ⟨ρ, hρ, hD⟩
  obtain ⟨ρ', hD'⟩ : ∃ ρ' : G →* Matrix (Fin n) (Fin n) κ', D.map f' = GDet.ofRep ρ' := by
    obtain ⟨r, -, hr⟩ := exists_semisimple_rep_of_detLaw_of_isAlgClosed (D.map f').toDet
    let ρ' := r.toMonoidHom.comp (MonoidAlgebra.of κ' G)
    have hrep : GDet.repAlg ρ' κ' = r := by
      apply MonoidAlgebra.algHom_ext
      · intro g
        simp [GDet.repAlg, ρ', MonoidAlgebra.lift_single]
      · ext
    refine ⟨ρ', Eq.symm ?_⟩
    suffices h : (GDet.ofRep ρ').toDet = (D.map f').toDet by
      rw [← GDet.ofDet_toDet (GDet.ofRep ρ'), h, GDet.ofDet_toDet]
    rw [← hr, ← hrep]
    refine Det.ext' fun S _ _ x => ?_
    change (GDet.repAlg ρ' S (ofT κ' G S x)).det = (Det.repS (GDet.repAlg ρ' κ') S x).det
    congr 1
    induction x with
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul s y =>
      rw [ofT_tmul, Det.repS_tmul, map_smul]
      congr 1
      induction y using MonoidAlgebra.induction_linear with
      | zero => ext i j; simp
      | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]; ext i j; simp
      | single g a => ext i j; simp [GDet.repAlg]
  refine ⟨ρ', ?_, hD'⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    exact (UpperTheory.V.AlgebraTools.Det.matIrrIff ⊤ ρ').2 (Subsingleton.elim _ _)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have htrace (K : Type) [Field K] (φ : A →+* K) (τ : G →* Matrix (Fin n) (Fin n) K)
      (hτ : D.map φ = GDet.ofRep τ) (g : G) :
      (τ g).trace = φ (D.tr (MonoidAlgebra.single g 1)) := by
    have hmap : (D.map φ).chi (MonoidAlgebra.single g 1) =
        (D.chi (MonoidAlgebra.single g 1)).map φ := by
      let _ : Algebra A K[X] := ((algebraMap K K[X]).comp φ).toAlgebra
      let ψ : A[X] →ₐ[A] K[X] :=
        { Polynomial.mapRingHom φ with commutes' := fun _ => Polynomial.map_C φ }
      have hψ (x : A[X]) : ψ x = x.map φ := rfl
      have h := D.nat A[X] K[X] ψ (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)
      simpa only [GDet.chi, GDet.map, map_sub, MonoidAlgebra.mapRingHom_single,
        AlgHom.coe_toRingHom, hψ, Polynomial.map_X, map_one] using h
    have hchi : (GDet.ofRep τ).chi (MonoidAlgebra.single g 1) = (τ g).charpoly := by
      simp only [GDet.chi, MonoidAlgebra.mapRingHom_single, map_one]
      change (GDet.repAlg τ K[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.single g 1)).det = _
      rw [map_sub, Matrix.charpoly]
      congr 1
      ext i j
      by_cases hij : i = j <;> simp [GDet.repAlg, hij]
    rw [hτ, hchi] at hmap
    rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, hmap]
    simp [GDet.tr, GDet.lam]
  let H : Subgroup G := ⊤
  obtain ⟨U, -, hU⟩ := UpperTheory.V.AlgebraTools.Det.irrOpen (ι := Fin n)
    (fun g : H => D.tr (MonoidAlgebra.single (g : G) 1))
  let p : PrimeSpectrum A := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  have hp : p ∈ U := (hU κ f (ρ.comp H.subtype) p rfl (fun g => htrace κ f ρ hD g)).2
    ((UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ).1 hρ)
  exact (UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ').2
    ((hU κ' f' (ρ'.comp H.subtype) p hker (fun g => htrace κ' f' ρ' hD' g)).1 hp)
