module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxDone
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeColumns.IdxCountStepOfModels

@[expose] public section

noncomputable section

namespace PIW.MassDataColumns

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets

def HModelAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word),
    X.MeasTie hb → X.LevelSubgroupNormalized → ∀ p : TypX X, HModelU X hb u p

theorem idxCountStep_of_modelAll (h : HModelAll) : IdxCountStep := idxCountStep_of_models h

end PIW.MassDataColumns
