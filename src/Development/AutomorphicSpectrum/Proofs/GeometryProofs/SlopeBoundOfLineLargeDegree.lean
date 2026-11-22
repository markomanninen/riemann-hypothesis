module

public import Mathlib
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLargeDegreeLineStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyDegreeOfBadReductionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyBadReductionHoldsStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem slopeBound_and_lemmaS_of_siegel :
    LineOfLargeDegree.Statement → SlopeBoundSt ∧ Prov.LemmaS := fun hS =>
  GlobalTheory.T.slope_bound_of_large_degree_line hS (GlobalTheory.T.key_degree_of_bad_reduction GlobalTheory.T.key_bad_reduction_holds)

end GlobalTheory.CompanionTheory.Ar.Sl
