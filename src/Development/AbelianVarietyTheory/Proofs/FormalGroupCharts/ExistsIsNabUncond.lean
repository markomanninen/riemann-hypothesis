module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTie
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndBC
public import Formalism.LocalToGlobal.ProjectiveLattices.IsExpChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsNab

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.CanonConn

theorem exists_isNab_uncond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∃ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab :=
  GlobalTheory.CanonConn.exists_isNab GlobalTheory.firstFiveLaws.1

end GlobalTheory.CanonConn
