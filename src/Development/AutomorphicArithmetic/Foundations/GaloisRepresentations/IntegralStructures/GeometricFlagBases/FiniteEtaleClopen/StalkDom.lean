module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

theorem UpperTheory.Gal.Int.Geo.Cut.stalkDom :
    UpperTheory.Gal.Int.Geo.Cut.StalkDom := by
  intro O _ _ _ Y p hp y
  haveI : Smooth p := hp
  haveI := GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth p y
  exact GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain
