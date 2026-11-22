module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetNormSqEqOneOfMemLatticeAut
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detNorm_eq_one_of_mem_autGL_var : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)), Submodule.IsFullLattice E Λ → ∀ γ ∈ autGL E j Λ, detNorm E j γ = 1 := by
  intro E _ _ hE j Λ hΛ γ hγ
  letI := hΛ
  exact GlobalTheory.OrbitTerm.detNorm_eq_one_of_mem_autGL E hE j Λ inferInstance γ hγ
