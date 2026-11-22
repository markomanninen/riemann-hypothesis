module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyClassSubsingletonOfAcyclicBounded
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheafCohomologyClass_subsingleton_of_acyclic_boundedBelow : ∀ (R : Type) [CommRing R] (G : Shv R) (M : Cx R) (a : ℤ) [M.IsStrictlyGE a], M.Acyclic → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (M.X t)) i)) → ∀ n : ℤ, Subsingleton (CohomologyClass (sgl G) M n) := by
  first | (exact @GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic) | (exact GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic) | (intros; apply GlobalTheory.EtC.subsingleton_cohomologyClass_sgl_of_acyclic  <;> assumption)
