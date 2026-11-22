module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MappingConeTermsSheafExtSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mappingCone_terms_sheafExt_subsingleton : ∀ (R : Type) [CommRing R] (G : Shv R) {C J : Cx R} (u : C ⟶ J), (∀ t, Injective (J.X t)) → (∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R (C.X t)) i)) → ∀ t i : ℤ, 0 < i → Subsingleton (CohomologyClass (sgl G) (res R ((mappingCone u).X t)) i) := by
  first | (exact @GlobalTheory.cone_terms_ext_subsingleton) | (exact GlobalTheory.cone_terms_ext_subsingleton) | (intros; apply GlobalTheory.cone_terms_ext_subsingleton  <;> assumption)
