module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsChartGOfBasis
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBiextDictionarySecondPartialLaw
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramesOfFormalChartStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.intChart : IntChartStatement :=
  intChart_of_cut
    (fun E _ _ _ H X0 t S _ _ x0 κ _ tg h1 h2 =>
      GlobalTheory.ChartData.exists_isChartG_of_basis E H X0 t S x0 κ tg h1 h2)
    (fun E _ _ _ H X0 t S _ _ x0 d G A κ _ tg uvec x h => GlobalTheory.T.exists_frames_of_formal_chart E H X0 t S x0 d G A κ tg uvec x h)
    GlobalTheory.FrameBiextId.fbId GlobalTheory.globalFns_holds
