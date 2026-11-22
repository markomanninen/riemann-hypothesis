module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ResolutionExistsOfResolutionStatementStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionExistsOfPoincareLelongStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeAndCoordinatesOfResolutionStatement
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ArithSystem
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFVert
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.EqZeroOfEventuallyEval
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRatioAlgDep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.GeoNum
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixedField
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ContractMixed
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Contract
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ProjContract
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Pub

open GroundTheory.Heights₂.Heights ReciprocityTheory.ChartRestriction.G.AI.I4

theorem contractMixed_closed : ContractMixedStatement :=
  have hIntZero : Inter.PFIntZero.Statement :=
    Inter.PFIntZero.proof (Inter.pointFormRank_holds.proof Inter.RatioAlgDep.proof)
  have hVert : Inter.PFVert.Statement :=
    Inter.PFVert.proof (by intros; exact geoNumStatement _)
      (by intros; exact Targets.ExistsUnique.full _ _) Targets.contractMixedField
  Targets.ContractMixed.of_found imageArith Targets.Contract.pulledBackForms_topDensity_vanish
    (Inter.ProjectivePointVertical.proof (by intros; exact geoNumStatement _)
      (by intros; exact Targets.ExistsUnique.full _ _)
      (by intros; exact Targets.ProjContract.full _ _ _ _ _))
    hIntZero hVert

theorem arithIntersectionSystem_of_poincareLelong_resK :
    GlobalTheory.CompanionTheory.Ar.Pub.PoincareLelong → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement := fun hPL hRK =>
  Targets.ArithIntersectionSystem.of_found
    (GlobalTheory.T.intersection_exists_of_poincare_lelong hPL (GlobalTheory.T.resolution_exists_of_resolution_statement hRK))
    (GlobalTheory.T.degree_and_coordinates_of_resolution (GlobalTheory.T.resolution_exists_of_resolution_statement hRK)).2
    contractMixed_closed

end GlobalTheory.CompanionTheory.Ar.Pub
