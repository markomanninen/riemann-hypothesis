module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallPacking
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRankBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecMRankBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsSeparated
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecEq
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConductor
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootGridLower
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGridSeparation
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNormalLocusRep
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjAvoidingForm
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSegreArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreRepresentatives
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAvoidFormFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormMax
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricMaxComparison
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFormsGeneric
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullRatiosAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullGradedAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomCharpoly
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomCharpolyForms
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormBadPrimesFinite
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormGoodPrimeIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormPrimeBound
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomRoots
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegreeInt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegralInt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomNormPIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartPrimePowerInverse
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFibreNormPullbackX
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PullbackConeNullModPHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormFormGaussBoundHoldsStatement

@[expose] public section

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel

namespace MultiProjectiveCoordinates

theorem pull_ratios_algebraic : PullRatiosAlgebraic.Statement :=
  PullRatiosAlgebraic.proof PullConeNull.proof PullConeDegree.proof PullGradedAlgebraic.proof

theorem pull_forms_generic : PullFormsGeneric.Statement := PullFormsGeneric.proof pull_ratios_algebraic

theorem fibre_pull_integral : FibreNormPullback.Statement :=
  FibreNormPullback.proof_dehom pull_forms_generic
    (FibreNormDehomCharpoly.proof pull_forms_generic pull_ratios_algebraic PullSectionIntegral.proof
      DehomCharpolyForms.proof)
    (FibreNormDehomIntegral.proof FibreNormBadPrimesFinite.proof
      (FibreNormGoodPrimeIntegral.proof GlobalTheory.T.pullback_cone_null_mod_p_holds PullConeDegreeInt.proof PullSectionIntegralInt.proof
        DehomNormPIntegral.proof)
      (FibreNormPrimeBound.proof pull_forms_generic GlobalTheory.T.norm_form_gauss_bound_holds ChartPrimePowerInverse.proof))
    FibreNormDehomRoots.full

theorem grid_separation : GridSeparation.Statement :=
  GridSeparation.proof NormalLocusRep.proof
    (FibreNormBound.proof (ProjAvoidingForm.proof SegreArith.proof)
      (FibreRepresentatives.proof AvoidFormFinite.proof)
      (FibreNormMax.proof fibre_pull_integral) MetricMaxComparison.proof)
    RootGridLower.proof

end MultiProjectiveCoordinates

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology in
theorem MultiProjectiveCoordinates.packing_statement : PackingStatement :=
  SmallPacking.proof
    (NmSectionsRankBound.proof (NmSectionsFinite.proof (Conductor.proof SecEq.proof)) SecMRankBound.full)
    (SmallSectionsSeparated.proof MultiProjectiveCoordinates.grid_separation)
