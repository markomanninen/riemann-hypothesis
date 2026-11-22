module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramedPointDiagonalBiextensionIsoCompati
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
theorem _root_.GlobalTheory.T.integralFramedPoint_diagonalBiextensionIso_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartPrimTrSt Xo c := by
  first | exact @GlobalTheory.chartPrimTr_holds | exact GlobalTheory.chartPrimTr_holds | (intros; apply GlobalTheory.chartPrimTr_holds <;> assumption)
