module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfNilpotentDividedPowersIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_of_nilpotentDividedPowers_ideal : ∀ {D : Type} [CommRing D] [Algebra ℂ D] {J : Ideal D} (dl : DividedPowers J), IsNilDP dl → IsNilpotent J := by
  first | exact @GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent | exact GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent | (intros; apply GlobalTheory.AnPer.isNilpotent_of_isDPNilpotent <;> assumption)
