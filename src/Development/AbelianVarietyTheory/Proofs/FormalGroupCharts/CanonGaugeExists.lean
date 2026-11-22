module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeOfLog
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PderivSecondEvFirstPointEqZero

@[expose] public section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem canonGauge_exists : CanonGaugeSt :=
  canonGauge_of_log FormalLog.logSt_and_logDerivSt.1

end GlobalTheory
