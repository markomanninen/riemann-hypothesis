module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussTop
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPoissonDual
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussSqrt
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPoissonBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeIsLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeCovolume
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussLatticeCoords
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussFourierSelf
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussDualMin
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussDetFactor
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussShellSum
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussShell
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussPacking
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussTermBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PGaussConstant
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaTop
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaMean
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaInnerMean
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaSummandNorm
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaCubeParseval
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaCharIntegral
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaNormMajorant
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaFirstCoordSplit
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PThetaConstants
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCauchyBinet
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPlueckerNormSq
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PHadamardPSD
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPlueckerUnitBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PPlueckerKernel
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PRootsOfUnityDense

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem GaussianSum.full : GaussianSum.Statement :=
  GaussianSum.proof
    (GaussPoissonDual.proof GaussSqrt.proof
      (GaussPoissonBound.proof GaussLatticeIsLattice.proof
        (GaussLatticeCovolume.proof GaussLatticeIsLattice.proof) GaussLatticeCoords.proof
        GaussFourierSelf.proof)
      GaussDualMin.proof GaussDetFactor.proof)
    (GaussShellSum.proof (GaussShell.proof GaussPacking.proof GaussTermBound.proof))
    GaussConstant.proof

theorem ThetaMean.full : ThetaMean.Statement :=
  ThetaMean.proof
    (ThetaInnerMean.proof ThetaSummandNorm.proof
      (ThetaCubeParseval.proof ThetaCharIntegral.proof))

theorem ThetaBound.full : ThetaBound.Statement :=
  ThetaBound.proof GaussianSum.full ThetaMean.full
    (ThetaNormMajorant.proof ThetaSummandNorm.proof) ThetaFirstCoordSplit.proof ThetaConstants.proof

theorem PlueckerNormSq.full : PlueckerNormSq.Statement := PlueckerNormSq.proof CauchyBinet.proof

theorem PlueckerUnitBound.full : PlueckerUnitBound.Statement :=
  PlueckerUnitBound.proof HadamardPSD.proof

theorem PlueckerKernel.full : PlueckerKernel.Statement :=
  PlueckerKernel.proof PlueckerNormSq.full PlueckerUnitBound.full

theorem RootsOfUnityDense.full : RootsOfUnityDense.Statement := RootsOfUnityDense.proof

end GroundTheory.Heights₂.Heights
