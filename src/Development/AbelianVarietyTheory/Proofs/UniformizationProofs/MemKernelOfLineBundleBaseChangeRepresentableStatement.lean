module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemKernelOfLineBundleBaseChangeRepresentable
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memKernelOfLineBundle_baseChange_representable : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (B : Over S) [GrpObj B] (L : LB B.left), L.IsLB → ∀ (H : Over S) (j : H ⟶ B), (∀ (T : Over S) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → ∀ (T' : Over S') (x : T' ⟶ (Over.pullback f).obj B), GlobalTheory.MemKL ((Over.pullback f).obj B) (L.pull (pullback.fst B.hom f)) x ↔ ∃ z : T' ⟶ (Over.pullback f).obj H, z ≫ (Over.pullback f).map j = x := by
  first | exact @GlobalTheory.memKL_baseChange_rep | exact GlobalTheory.memKL_baseChange_rep | (intros; apply GlobalTheory.memKL_baseChange_rep <;> assumption)
