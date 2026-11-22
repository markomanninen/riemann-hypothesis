module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjDegGenDeg
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRankOfSections
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertPrime
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertIncrement
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PIntersectionRecursion
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedHilbertPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PModulesFromPrimes
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedFiltration
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiltrationHilbSum
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegLTGrowth

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

open GroundTheory.Heights₂.Heights.HilbertSamuel

theorem HilbertPrime.closed : HilbertPrime.Statement.{0} :=
  HilbertPrime.proof HilbertDimZero.proof (HilbertIncrement.proof IntersectionRecursion.proof)
    (MixedNumberPolynomial.proof (MultigradedHilbertPolynomial.proof EventualPolynomial.proof))
    (ModulesFromPrimes.proof MultigradedFiltration.proof FiltrationHilbSum.proof DegLTGrowth.proof)

theorem RankOfSections.closed : RankOfSections.Statement :=
  RankOfSections.proof HilbertPrime.closed
    (MixedNumberPolynomial.proof (MultigradedHilbertPolynomial.proof EventualPolynomial.proof))

theorem ProjDegGenDeg.proof : ProjDegGenDeg.Statement :=
  HilbertSamuel.ProjDegGenDeg.proof RankOfSections.closed

end GroundTheory.Heights₂.Heights.Swarm
