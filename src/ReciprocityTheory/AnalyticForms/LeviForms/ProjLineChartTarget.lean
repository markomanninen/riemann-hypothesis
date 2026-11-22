module

public import ReciprocityTheory.AnalyticForms.LeviForms.ProjectiveLineSecondChartSymmOfNe

@[expose] public section

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

abbrev T0 : ℝ := Real.exp (-Real.exp (Real.exp 1))

section RM

open ReciprocityTheory.AnForm.A

end RM

end

end ReciprocityTheory.AnForm.P
