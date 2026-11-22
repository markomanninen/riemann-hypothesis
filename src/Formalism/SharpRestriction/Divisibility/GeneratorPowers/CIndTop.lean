module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndAll
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFixAsm
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrRatio
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGauge

@[expose] public section

set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField

theorem chartIndep2_of_gauge_glob (hGauge : ExpGaugeOfSt) (hGlob : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) : ChartIndepSt2 :=
  chartIndep2_of_gauge hGauge hGlob frTruncFix_holds

theorem chartIndep2_of_glob (hGlob : ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt) : ChartIndepSt2 :=
  chartIndep2_of_gauge_glob (ExpGauge.expGaugeOf_of (expActOf_of linEigSt_holds)) hGlob


end Formalism.MainNotions.ModuliIntegralCharts.H1
