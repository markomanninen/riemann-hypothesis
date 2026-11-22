module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaConjugateMeanLogAbsBoundOfTransport
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport

@[expose] public section

open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.betaConjugate_mean_logAbs_bound_of_transport : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → FieldDat → LBound → TorEx → BetaArch := by
  first | exact @GlobalTheory.SqTop.betaArch_of_transport | exact GlobalTheory.SqTop.betaArch_of_transport | (intros; apply GlobalTheory.SqTop.betaArch_of_transport <;> assumption)
