module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PTConclAt

@[expose] public section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace GlobalTheory.CompanionTheory.FieldModel

theorem exists_subfield_model : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω], ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : NumberField K) (_ : IsAlgClosure K (AlgebraicClosure ℚ)) (e : F ≃+* K) (E : Ω ≃+* (AlgebraicClosure ℚ)), ∀ x : F, E (algebraMap F Ω x) = algebraMap K (AlgebraicClosure ℚ) (e x) := by
  intro F Ω _ _ _ _ _
  let σ : F →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let e : F ≃ₐ[ℚ] σ.fieldRange := AlgEquiv.ofInjectiveField σ
  haveI fd : FiniteDimensional ℚ σ.fieldRange := e.toLinearEquiv.finiteDimensional
  haveI nf : NumberField σ.fieldRange := { to_charZero := inferInstance, to_finiteDimensional := fd }
  haveI alg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    have h : @Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) :=
      (AlgebraicClosure.isAlgebraic ℚ)
    convert h
  haveI ac : IsAlgClosure σ.fieldRange (AlgebraicClosure ℚ) :=
    ⟨AlgebraicClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) σ.fieldRange⟩
  refine ⟨σ.fieldRange, nf, ac, e.toRingEquiv, IsAlgClosure.equivOfEquiv Ω (AlgebraicClosure ℚ) e.toRingEquiv, fun x => ?_⟩
  exact IsAlgClosure.equivOfEquiv_algebraMap Ω (AlgebraicClosure ℚ) e.toRingEquiv x

end GlobalTheory.CompanionTheory.FieldModel
