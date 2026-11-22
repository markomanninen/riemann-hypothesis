module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif

@[expose] public section

open GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positivity_statement : GlobalTheory.CompanionTheory.Jp.JpPos := by
  first | exact @GlobalTheory.CompanionTheory.Jp.Pos.jpPos | exact GlobalTheory.CompanionTheory.Jp.Pos.jpPos | (intros; apply GlobalTheory.CompanionTheory.Jp.Pos.jpPos <;> assumption)
