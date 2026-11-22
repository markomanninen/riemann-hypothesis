module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SimplePoleTwistedLift
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont

@[expose] public section

namespace GlobalTheory.LiftPoleObj

theorem simplePole_of_hecke (hH : GlobalTheory.Published.HeckeLPartialContinuation) : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole :=
  GlobalTheory.LiftPole.simplePole_of_hecke hH

end GlobalTheory.LiftPoleObj
