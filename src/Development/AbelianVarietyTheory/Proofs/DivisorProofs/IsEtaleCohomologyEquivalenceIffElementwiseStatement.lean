module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCohomologyEquivalenceIffElementwise
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCohomologyEquivalence_iff_elementwise : ∀ (R : Type) [CommRing R] (F : Shv R) (E E' : Spc) (f : E ⟶ E'), Eqv R f F ↔ SurjH ((HC R F).map f.op) ∧ InjH ((HC R F).map f.op) := by
  first | (exact @GlobalTheory.EtC.HCEqv.main) | (exact GlobalTheory.EtC.HCEqv.main) | (intros; apply GlobalTheory.EtC.HCEqv.main  <;> assumption)
