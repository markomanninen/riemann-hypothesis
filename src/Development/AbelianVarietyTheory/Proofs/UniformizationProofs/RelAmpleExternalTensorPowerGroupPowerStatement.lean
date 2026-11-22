module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.relAmple_externalTensorPower_groupPower : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j) (L : LB G.left), L.IsLB → RelAmple G L → RelAmple G' (boxLB L p.pr) := by
  first | exact @GlobalTheory.relAmple_boxLB | exact GlobalTheory.relAmple_boxLB | (intros; apply GlobalTheory.relAmple_boxLB <;> assumption)
