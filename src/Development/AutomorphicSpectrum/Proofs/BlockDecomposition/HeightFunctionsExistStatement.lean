module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExist
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_functions_exist : HtExist := by
  first | exact @GlobalTheory.CompanionTheory.HtEx.htExist | exact GlobalTheory.CompanionTheory.HtEx.htExist | (intros; apply GlobalTheory.CompanionTheory.HtEx.htExist <;> assumption)
