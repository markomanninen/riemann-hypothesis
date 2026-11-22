module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisation_baseChange : PolBaseChangeSt → GlobalFnsSt → SecBaseChangeSt → DVR.TwistBaseChangeStatement → UnifBaseChangeSt := by
  first | exact @GlobalTheory.unifBaseChange | exact GlobalTheory.unifBaseChange | (intros; apply GlobalTheory.unifBaseChange <;> assumption)
