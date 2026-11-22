module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenPoly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIsolatedFibreOpenFixed
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ImportsAlt
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IsolatedFibreOpenPoly.full : IsolatedFibreOpenPoly.Statement :=
  IsolatedFibreOpenPoly.proof
    (IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric.proof
      (IndefiniteRowSideFullHecke.ComplexSets.GenericProjectionFinite.equiv.mp ComplexSets.GenericProjectionFinite.full)
      IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.full)

end GroundTheory.Heights₂.Heights
