module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegGeomDeg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem genDegGeomDeg_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement :=
  fun hI _ => GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.proof
    (degreeGeneric_of_degree (degree_of_system hI))

end GlobalTheory.CompanionTheory.Ar.Giv
