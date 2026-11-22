module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveProjBundleModelCochainComplexX
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_projBundleModelCochainComplex_X : ∀ (R : Type) [CommRing R] (q N : ℕ) (I : Cx R), (∀ n, CategoryTheory.Injective (I.X n)) → ∀ n, CategoryTheory.Injective ((Jcx R q N I).X n) := by
  first | (exact @GlobalTheory.EtC.Jcx_X_injective) | (exact GlobalTheory.EtC.Jcx_X_injective) | (intros; apply GlobalTheory.EtC.Jcx_X_injective  <;> assumption)
