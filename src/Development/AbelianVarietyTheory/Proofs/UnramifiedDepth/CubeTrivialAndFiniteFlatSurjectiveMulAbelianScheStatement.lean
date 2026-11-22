module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubeTrivialAndFiniteFlatSurjectiveMulAbelianSche
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.TowerZeroSurjective
public import ReciprocityTheory.DualLattices.LinPairStatement
public import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.SubMemOfCompat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cube_trivial_and_finite_flat_surjective_mul_abelianScheme : ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (M : LB G.left) (Q : LB (G ⊗ G).left), IsAbelianScheme G → M.IsLB → Out.RelAmple G M → Q.IsLB → (∃ θ : LB.Gen (Theta (G ⊗ G) Q), θ.IsGen) ∧ ∀ n : ℕ, 1 ≤ n → IsFinite ((𝟙 G) ^ n : G ⟶ G).left ∧ Flat ((𝟙 G) ^ n : G ⟶ G).left ∧ Surjective ((𝟙 G) ^ n : G ⟶ G).left := by
  first | exact @GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow | exact GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow | (intros; apply GlobalTheory.ChF.exists_gen_theta_tensor_and_finite_flat_surjective_pow <;> assumption)
