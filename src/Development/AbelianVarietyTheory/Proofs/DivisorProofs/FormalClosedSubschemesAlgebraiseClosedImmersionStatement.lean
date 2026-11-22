module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalClosedSubschemesAlgebraiseClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalClosedSubschemesAlgebraise_closedImmersion : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (i : W' ⟶ W), IsSeparated f → IsClosedImmersion i → Alg f I → Alg (i ≫ f) I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_isClosedImmersion | exact GlobalTheory.FormalAlg.alg_of_isClosedImmersion | (intros; apply GlobalTheory.FormalAlg.alg_of_isClosedImmersion <;> assumption)
