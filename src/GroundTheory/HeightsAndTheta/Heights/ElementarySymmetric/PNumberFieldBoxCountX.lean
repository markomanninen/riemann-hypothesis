module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PNumberFieldBoxCount
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLatticeImageZLattice
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCovolumeRelIndex
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PEmbeddingSumPlaces
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PMixedBoxCount
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLatticeCountVolume

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem NumberFieldBoxCount.proof_closed : NumberFieldBoxCount.Statement :=
  NumberFieldBoxCount.proof LatticeImageZLattice.proof CovolumeRelIndex.proof EmbeddingSumPlaces.proof
    (MixedBoxCount.proof LatticeCountVolume.proof)

end GroundTheory.Heights₂.Heights.Targets
