module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelExistsBis
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

@[expose] public section

open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_exists_bis : LevelEx := by
  first | exact @GlobalTheory.CompanionTheory.LevelU.levelEx | exact GlobalTheory.CompanionTheory.LevelU.levelEx | (intros; apply GlobalTheory.CompanionTheory.LevelU.levelEx <;> assumption)
