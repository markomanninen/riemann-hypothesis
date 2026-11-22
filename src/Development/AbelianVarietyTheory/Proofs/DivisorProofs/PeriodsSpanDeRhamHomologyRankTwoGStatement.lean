module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSpanDeRhamHomologyRankTwoG
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_span_deRhamHomology_rank_two_g : PSpan := by
  first | exact @GlobalTheory.PeriodSpan.main | exact GlobalTheory.PeriodSpan.main | (intros; apply GlobalTheory.PeriodSpan.main <;> assumption)
