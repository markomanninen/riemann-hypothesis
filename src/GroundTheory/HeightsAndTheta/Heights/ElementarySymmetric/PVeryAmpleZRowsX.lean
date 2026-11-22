module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZRows
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechPartition
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZChartSmul
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PZChartLocal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem VeryAmpleZRows.proof_closed : VeryAmpleZRows.Statement.{u, v, w} :=
  VeryAmpleZRows.proof CechPartition.proof ZChartSmul.proof (ZChartLocal.proof ZChartSmul.proof)

end GroundTheory.Heights₂.Heights.Kleiman
