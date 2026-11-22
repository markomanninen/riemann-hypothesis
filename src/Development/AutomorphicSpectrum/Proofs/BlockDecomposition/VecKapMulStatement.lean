module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecKapMul
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_term_identity : Term := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTerm.term | exact GlobalTheory.CompanionTheory.RgEisTerm.term | (intros; apply GlobalTheory.CompanionTheory.RgEisTerm.term <;> assumption)
