module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauINontrivial
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CoordIdealIsMultiProjPrime
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltMore
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqCech

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

theorem serreVanishing_graded_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman.SerreVanish.Statement :=
  (GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv
    GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof).1
    GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.full.{0, 0}

end

end GroundTheory.Heights₂.Heights.KeyFormula
