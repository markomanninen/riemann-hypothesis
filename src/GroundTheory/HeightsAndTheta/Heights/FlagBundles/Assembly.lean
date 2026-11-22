module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
public import GroundTheory.PAdicHodge.SlopeCauchyBinet
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGKernelIdentity
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalKernel
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereLongitudeCoordinates
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalHeightReduction
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalKernelPairing
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalBilinearFormula
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGHatIdentity
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreConstantClosedForm
public import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreIntegralInvariant
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudyIntegral

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

theorem GKernelIdentity.full : GKernelIdentity.Statement :=
  GKernelIdentity.proof

theorem ZonalKernel.full : ZonalKernel.Statement :=
  ZonalKernel.proof

theorem SphereLongitudeCoordinates.full : SphereLongitudeCoordinates.Statement :=
  SphereLongitudeCoordinates.proof

theorem ZonalHeightReduction.full : ZonalHeightReduction.Statement :=
  ZonalHeightReduction.proof SphereLongitudeCoordinates.full ZonalKernel.full

theorem ZonalKernelPairing.full : ZonalKernelPairing.Statement :=
  ZonalKernelPairing.proof

theorem ZonalBilinearFormula.full : ZonalBilinearFormula.Statement :=
  ZonalBilinearFormula.proof ZonalHeightReduction.full ZonalKernelPairing.full

theorem GHatIdentity.full : GHatIdentity.Statement :=
  GHatIdentity.proof GKernelIdentity.full

theorem FibreConstantClosedForm.full : FibreConstantClosedForm.Statement :=
  FibreConstantClosedForm.proof ZonalBilinearFormula.full GHatIdentity.full

theorem fibreConstant_eq (k : ℕ) :
    fibreConstant k = -(1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1) :=
  FibreConstantClosedForm.full.1 k

theorem FibreIntegralInvariant.full : FibreIntegralInvariant.Statement :=
  FibreIntegralInvariant.proof FibreConstantClosedForm.full

end GroundTheory.Heights₂.Heights.FlagBundles
