module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianSchemeTorsionRepresentation
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
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
open GlobalTheory.CompanionTheory.Ar.GR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_scheme_torsion_representation : ∀ (R : Type) [CommRing R] [IsLocalRing R] (p : ℕ), 1 ≤ p → ∀ (A : Over (Spec (CommRingCat.of R))) [GrpObj A] (L : LB A.left), IsAbelianScheme A → L.IsLB → Out.RelAmple A L → Nonempty (TorsRep A p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.torsRep_nonempty_of_relAmple | exact GlobalTheory.CompanionTheory.Ar.GR.torsRep_nonempty_of_relAmple | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.torsRep_nonempty_of_relAmple <;> assumption)
