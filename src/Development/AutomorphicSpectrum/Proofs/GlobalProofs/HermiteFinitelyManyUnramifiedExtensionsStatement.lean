module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermiteFinitelyManyUnramifiedExtensions
public import ReciprocityTheory.Hypotheses.GalCoh
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
public import GroundTheory.ProfiniteCohomology.ContinuousCochains

@[expose] public section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermite_finitely_many_unramified_extensions : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Finset (HeightOneSpectrum (𝓞 F))) (N : ℕ), {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside (S : Set (HeightOneSpectrum (𝓞 F))) E ∧ Module.finrank F E ≤ N}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree | exact GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree | (intros; apply GlobalTheory.CompanionTheory.HermiteMinkowski.finite_unramified_bounded_degree <;> assumption)
