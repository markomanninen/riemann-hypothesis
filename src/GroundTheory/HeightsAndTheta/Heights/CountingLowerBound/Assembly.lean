module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PInteriorDichotomy
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMinkowskiCovolumeBound
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PCuspWeightBound
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PShortVectorsOrthogonal
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PPackingCount
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanCountBound
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PTailBound
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanLogPlus
public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanCuspWeight

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

universe u

theorem PackingCount.full : PackingCount.Statement :=
  PackingCount.proof

theorem MeanCountBound.full : MeanCountBound.Statement.{u} :=
  MeanCountBound.proof

theorem TailBound.full : TailBound.Statement.{u} :=
  TailBound.proof MeanCountBound.full

theorem MeanLogPlus.full : MeanLogPlus.Statement.{u} :=
  MeanLogPlus.proof TailBound.full

theorem MeanCuspWeight.full : MeanCuspWeight.Statement :=
  MeanCuspWeight.proof

end GroundTheory.Heights₂.Heights.LowerBound
