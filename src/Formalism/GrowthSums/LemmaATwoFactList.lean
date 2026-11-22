module

public import Formalism.GrowthSums.FactorialBaseGrowth.Coarse
public import Formalism.GrowthSums.FactorialBaseGrowth.Harmonic
public import Formalism.GrowthSums.FactorialBaseGrowth.QuadraticExponentIdentity
public import Formalism.GrowthSums.FactorialBaseGrowth.Segment
public import Formalism.GrowthSums.FactorialBaseGrowth.NextEvenTopHolds
public import Formalism.GrowthSums.FactorialBaseGrowth.LogCoef
public import Mathlib
public import Formalism.GrowthSums.FactorialBaseGrowth.PathBasisOfCount

@[expose] public section

namespace Formalism.GrowthSums.Top

theorem segmentBound : Formalism.GrowthSums.SegmentBound := Formalism.GrowthSums.segment_bound_holds
theorem nextEvenTop : Formalism.GrowthSums.NextEvenTop := Formalism.GrowthSums.next_even_top_holds
theorem topCount : Formalism.GrowthSums.TopCount := Formalism.GrowthSums.top_count_holds

end Formalism.GrowthSums.Top
