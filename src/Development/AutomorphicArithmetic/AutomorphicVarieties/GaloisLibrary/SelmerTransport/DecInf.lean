module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.IneOpen

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

private theorem exists_unit (l : ℕ) [hl : Fact l.Prime] : ∃ u : ℤ_[l]ˣ, ¬ IsOfFinOrder u := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl2 := hl.out.two_le
  have hnorm : ‖((1 + l : ℕ) : ℤ_[l])‖ = 1 := by
    push_cast
    rw [PadicInt.norm_add_eq_max_of_ne, norm_one, PadicInt.norm_p]
    · exact max_eq_left (inv_le_one_of_one_le₀ hl1.le)
    · rw [norm_one, PadicInt.norm_p]
      exact (inv_lt_one_of_one_lt₀ hl1).ne'
  obtain ⟨u, hu⟩ := PadicInt.isUnit_iff.2 hnorm
  refine ⟨u, fun h => ?_⟩
  rw [← Units.isOfFinOrder_val, hu, isOfFinOrder_iff_pow_eq_one] at h
  obtain ⟨n, hn, h⟩ := h
  rw [← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h
  omega

theorem UpperTheory.V.Base.decInf :
    ∀ (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G k Ω)), IsOpen (U : Set (G k Ω)) → ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
      ∃ g ∈ U ⊓ Dec (F := k) A, ¬ IsOfFinOrder (cycZ k Ω l g) := by
  intro k Ω _ _ _ _ _ l _ U hU A hlt
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ k Ω
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨u, hu⟩ := exists_unit l
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hlt u
  let K : IntermediateField ℚ Ω := (IsScalarTower.toAlgHom ℚ k Ω).fieldRange
  have : FiniteDimensional ℚ K :=
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ k Ω)).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[ℚ] Ω) ⧸ K.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ K.fixingSubgroup_isOpen
  have : K.fixingSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.FiniteIndex.index_ne_zero (H := K.fixingSubgroup)) σ
  let g : G k Ω := { (σ ^ n).toRingEquiv with
    commutes' := fun x => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _ ⟨x, rfl⟩ }
  have hg : g ∈ Dec (F := k) A := (Dec (F := ℚ) A).pow_mem (Ine_le_Dec A hσ) n
  have hgu : cycZ k Ω l g = u ^ n := by
    change cycZ ℚ Ω l (σ ^ n) = u ^ n
    rw [map_pow, hσu]
  haveI : Finite (G k Ω ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI := Subgroup.finiteIndex_normalCore U
  haveI := Subgroup.normalCore_normal U
  have hN : U.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hgU : g ^ U.normalCore.index ∈ U := U.normalCore_le (Subgroup.pow_index_mem _ g)
  refine ⟨g ^ U.normalCore.index, ⟨hgU, Subgroup.pow_mem (Dec (F := k) A) hg _⟩, ?_⟩
  rw [map_pow, hgu, ← pow_mul, isOfFinOrder_pow]
  rintro (h | h)
  · exact hu h
  · exact mul_ne_zero hn.ne' hN h
