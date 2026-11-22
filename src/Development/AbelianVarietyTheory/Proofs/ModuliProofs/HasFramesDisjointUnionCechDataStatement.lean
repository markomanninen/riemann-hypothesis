module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesDisjointUnionCechData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFrames_disjointUnionCechData : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A B : LB Z) (n : ℕ) (r s : ℤ), (∀ i j, A.U i ⊓ B.U j = ⊥) → HasFrames G L N A n r s → HasFrames G L N B n r s → HasFrames G L N (sumLB A B) n r s := by
  first | exact @GlobalTheory.ModelSum.hasFrames_sumLB | exact GlobalTheory.ModelSum.hasFrames_sumLB | (intros; apply GlobalTheory.ModelSum.hasFrames_sumLB <;> assumption)
