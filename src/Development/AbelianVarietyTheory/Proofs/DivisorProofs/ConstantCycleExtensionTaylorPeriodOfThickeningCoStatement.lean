module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCycleExtensionTaylorPeriodOfThickeningCo
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCycleExtension_taylorPeriod_of_thickeningComparison : GlobalTheory.AnPer.PTaylor := by
  first | exact @GlobalTheory.AnPer.pTaylor | exact GlobalTheory.AnPer.pTaylor | (intros; apply GlobalTheory.AnPer.pTaylor <;> assumption)
