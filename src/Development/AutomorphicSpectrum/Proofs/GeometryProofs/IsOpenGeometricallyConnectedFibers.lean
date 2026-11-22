module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricConnectednessGeneralizesStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConnectedFibersStableUnderSpecializationStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConstructibleStableOpenStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem isOpen_geometricallyConnected_fibres :
    ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (G : Over (Sp k)) [GrpObj G] [IsCommMonObj G],
      Smooth G.hom → IsProper G.hom →
      IsOpen {x : PrimeSpectrum k | GeometricallyConnected
        (pullback.snd G.hom (spMap (algebraMap k x.asIdeal.ResidueField)))} := by
  intro k _ _ G _ _ hs hp
  have hgen := GlobalTheory.T.geometric_connectedness_generalizes k G.left G.hom (η[G]).left (Over.w η[G]) hs hp
  have hspec := GlobalTheory.T.connected_fibers_stableUnderSpecialization k G hs hp
  exact GlobalTheory.T.isOpen_of_stable_under_generalization_specialization k _ hgen hspec

end GlobalTheory.CompanionTheory.Ar.Approx
