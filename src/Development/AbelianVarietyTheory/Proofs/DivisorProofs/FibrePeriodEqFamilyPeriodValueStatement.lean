module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePeriodEqFamilyPeriodValue
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibrePeriod_eq_familyPeriod_value : PFix := by
  first | exact @GlobalTheory.AnPer.period_fibre_eq_value | exact GlobalTheory.AnPer.period_fibre_eq_value | (intros; apply GlobalTheory.AnPer.period_fibre_eq_value <;> assumption)
