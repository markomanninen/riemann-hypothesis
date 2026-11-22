module

public import ReciprocityTheory.SemistableReduction.SemiDeg
public import ReciprocityTheory.SemistableReduction.SemiContract
public import ReciprocityTheory.SemistableReduction.LatAll

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem semiPoint : SemiPointStatement := semiDeg_holds degAdd

theorem semistable : SemistableStatement := semiContract_holds semiPoint degAdd

end ReciprocityTheory.MultiplicativeHeights.Closed
