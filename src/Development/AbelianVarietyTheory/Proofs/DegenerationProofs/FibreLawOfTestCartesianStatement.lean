module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesian
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.fibreLaw_of_testCartesian : ∀ C : Core, C.TestCart → C.FibLaw := by
  first | exact @GlobalTheory.ZJ.Core.fibLaw_of_testCart | exact GlobalTheory.ZJ.Core.fibLaw_of_testCart | (intros; apply GlobalTheory.ZJ.Core.fibLaw_of_testCart <;> assumption)
