module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleUnitaryGroupConcrete
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_unitaryGroup_concrete : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple := by
  first | exact @GlobalTheory.RegSSObj.regularSemisimple | exact GlobalTheory.RegSSObj.regularSemisimple | (intros; apply GlobalTheory.RegSSObj.regularSemisimple <;> assumption)
