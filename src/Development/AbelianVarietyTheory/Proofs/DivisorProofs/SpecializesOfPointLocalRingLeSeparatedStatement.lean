module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesOfPointLocalRingLeSeparated
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace

@[expose] public section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specializes_of_pointLocalRing_le_separated : ∀ (X : Scheme.{0}) [IsIntegral X] [X.IsSeparated] (x z : X), locRing x ≤ locRing z → z ⤳ x := by
  first | exact @GlobalTheory.specializes_of_locRing_le | exact GlobalTheory.specializes_of_locRing_le | (intros; apply GlobalTheory.specializes_of_locRing_le <;> assumption)
