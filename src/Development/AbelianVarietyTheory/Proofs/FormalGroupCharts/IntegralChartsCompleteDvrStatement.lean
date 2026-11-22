module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralChartsCompleteDvr
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_charts_complete_dvr : IntChartStatement := by
  first | exact @GlobalTheory.intChart | exact GlobalTheory.intChart | (intros; apply GlobalTheory.intChart <;> assumption)
