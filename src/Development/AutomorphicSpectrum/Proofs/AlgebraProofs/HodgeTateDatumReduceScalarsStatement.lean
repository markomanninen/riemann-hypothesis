module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateDatumReduceScalars
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
theorem _root_.GlobalTheory.T.hodge_tate_datum_reduce_scalars : ∀ (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] (Oe : Type) [CommRing Oe] [Algebra ℤ_[p] Oe] (σ : Oe ≃ₐ[ℤ_[p]] Oe) (cp : R), HodgeTateSetting p v R Oe σ cp → ∀ H : HodgeTateDatum p g v R Oe σ cp, HodgeTateSetting p v R ℤ_[p] AlgEquiv.refl cp ∧ ∃ H' : HodgeTateDatum p g v R ℤ_[p] AlgEquiv.refl cp, H'.AA = H.AA ∧ H'.Ht = H.Ht ∧ H'.Bt = H.Bt ∧ H'.E = H.E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.htd_restrict_coefficients | exact GlobalTheory.CompanionTheory.Ar.GR.htd_restrict_coefficients | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.htd_restrict_coefficients <;> assumption)
