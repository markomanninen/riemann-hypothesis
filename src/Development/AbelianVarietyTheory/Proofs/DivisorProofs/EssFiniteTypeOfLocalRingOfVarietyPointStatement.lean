module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalRingOfVarietyPoint
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K),
  IsLocModel (algebraMap ℂ K) R → Algebra.EssFiniteType ℂ K := by
  first | exact @GlobalTheory.essFiniteType_of_isLocModel | exact GlobalTheory.essFiniteType_of_isLocModel | (intros; apply GlobalTheory.essFiniteType_of_isLocModel <;> assumption)
