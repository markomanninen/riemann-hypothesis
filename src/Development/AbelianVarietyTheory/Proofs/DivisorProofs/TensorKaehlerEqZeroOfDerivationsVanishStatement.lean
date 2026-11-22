module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorKaehlerEqZeroOfDerivationsVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_liftBaseChange_derivations_eq_zero : ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C], Module.Projective C Ω[C⁄R] → ∀ z : B ⊗[R] Ω[C⁄R], (∀ θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C, (∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) → LinearMap.liftBaseChange B θ z = 0) → z = 0 := by
  first | exact @GlobalTheory.tensor_kaehler_eq_zero_of_derivations_vanish | exact GlobalTheory.tensor_kaehler_eq_zero_of_derivations_vanish | (intros; apply GlobalTheory.tensor_kaehler_eq_zero_of_derivations_vanish <;> assumption)
