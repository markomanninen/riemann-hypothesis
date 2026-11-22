module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodHom
public import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSpanTopAndFinrankFromCechPeriodsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallinePeriodEqCechDeRhamPeriodStatement

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PeriodSpan

theorem main : PSpan := by
  intro A _ g hA _ L u P hP
  exact GlobalTheory.T.period_map_span_top_and_finrank_from_cech_periods A g L u hA P fun c =>
    GlobalTheory.T.crystalline_period_eq_cechDeRham_period A g L u c.1
      { toFun := fun l => P l c, map_zero' := by simp, map_add' := fun x y => by simp }
      _ (fun _ => rfl) (hP c)

end GlobalTheory.PeriodSpan
