module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicUniformizationDimEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ContinuousOnValue
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_uniformization_dim_eq : ∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g d : ℕ) (u : HolUnif A L g), SmoothOfRelativeDimension d A.hom → g = d := by
  first | exact @GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension | exact GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension | (intros; apply GlobalTheory.CompanionTheory.Ar.UnifDim.eq_relativeDimension <;> assumption)
