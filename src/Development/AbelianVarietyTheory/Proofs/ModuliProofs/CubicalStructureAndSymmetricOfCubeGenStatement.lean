module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.cubicalStructure_and_symmetric_of_cube_gen : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsSemiAbelian G → (IsReduced X ∧ genericPoints X ⊆ abLocus G) → ((∃ t : (Theta G L.L).Gen, t.IsGen) → Nonempty (CubicalStr G L)) ∧ (LBIso L.L (L.L.pull (GrpObj.inv (X := G)).left) → L.IsSymmetric) := by
  first | exact @GlobalTheory.CubeGen.cubical_and_symmetric | exact GlobalTheory.CubeGen.cubical_and_symmetric | (intros; apply GlobalTheory.CubeGen.cubical_and_symmetric <;> assumption)
