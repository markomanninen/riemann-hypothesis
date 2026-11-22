module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.UpdateEraseSubset
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GraphEquiv
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.DoubleSumEqZero

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem DoubleCech.proof : GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.DoubleCech.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.DoubleCech.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.Staircase.proof
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq.proof

end GroundTheory.Heights₂.Heights.Swarm
