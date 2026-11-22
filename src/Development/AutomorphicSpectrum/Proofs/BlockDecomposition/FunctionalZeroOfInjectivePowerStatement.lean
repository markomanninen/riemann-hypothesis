module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalZeroOfInjectivePower
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff

@[expose] public section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functional_zero_of_injective_power : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (A : V →ₗ[ℂ] V), Function.Injective A → ∀ (l : V →ₗ[ℂ] ℂ) (v : V) (j₀ : ℕ), (∀ j ≥ j₀, l ((A ^ j) v) = 0) → l v = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates | exact GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates | (intros; apply GlobalTheory.CompanionTheory.SatPow.functional_eq_zero_of_late_iterates <;> assumption)
