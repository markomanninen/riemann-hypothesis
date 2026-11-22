module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleOf

@[expose] public section

namespace GlobalTheory.RegSSObj

theorem regularSemisimple : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple :=
  GlobalTheory.RegSS.regularSemisimple

end GlobalTheory.RegSSObj
