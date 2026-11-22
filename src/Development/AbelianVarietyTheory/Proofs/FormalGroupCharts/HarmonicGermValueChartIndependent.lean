module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerb
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EvalSinglePointId
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.KillAddVal
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PsiCover
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.HarmInvPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFixAsm
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGauge
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.FrTruncFixIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

@[expose] public section

namespace GlobalTheory

open Formalism.MainNotions.ModuliIntegralCharts.H1

theorem harmonicValue_chart_independent : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 := by
  have hAct : ExpActOfSt := by
    refine expActOf_of_eig ?_
    intro E _ _ _ H Dw l Xo c _ S _ _ _ y C a ℓ i
    exact EigDir.linEig_holds E H Dw l Xo c S y C a ℓ i
  refine chartIndep2_verb ?_ (GlobalTheory.BalancedTwist.frTruncFix_iff.mp frTruncFix_holds) germFix_holds (harmInv_of hAct)
  refine chartIndepTrunc_of (expChartOf_of hAct) (ExpGauge.expGaugeOf_of hAct) tie_holds ExpUniqChart.expUniqTan
    (gaugeUniq_of_global globalFns_holds) (killAddVal_of ?_)
  intro E _ _ _ H
  exact psiCover_holds H

end GlobalTheory
