module

public import ReciprocityTheory.SemistableReduction.LemmaH
public import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
public import ReciprocityTheory.SemistableReduction.ApproxGraph
public import ReciprocityTheory.SemistableReduction.ApproxBasis
public import ReciprocityTheory.SemistableReduction.Unipotent
public import ReciprocityTheory.SemistableReduction.DegAddHolds
public import ReciprocityTheory.SemistableReduction.OnePolyGrowth
public import ReciprocityTheory.SemistableReduction.BWPoly
public import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem approx : ApproxStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.approxBasis_holds ReciprocityTheory.MultiplicativeHeights.approxGraph_holds

theorem degAdd : DegAddStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.degAdd_holds

theorem bwPoly : BWPolyStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.bwPoly_holds ReciprocityTheory.MultiplicativeHeights.lemmaH_holds ReciprocityTheory.L2DbarEstimates.ext
    ReciprocityTheory.MultiplicativeHeights.onePolyGrowth_holds

end ReciprocityTheory.MultiplicativeHeights.Closed
