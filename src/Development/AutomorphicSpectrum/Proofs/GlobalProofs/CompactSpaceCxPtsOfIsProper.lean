module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactSpacePts
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.WeilBound.CoreStatements.ProjectiveValuations.CompactSpaceComplexPointsOfProper

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem compactSpace_cxPts_of_isProper :
    ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProper p → CompactSpace (CxPts p (RingHom.id ℂ)) :=
  DifferentiableLines.compactSpace_complex_points_of_proper

end GlobalTheory.CompanionTheory.Gaga
