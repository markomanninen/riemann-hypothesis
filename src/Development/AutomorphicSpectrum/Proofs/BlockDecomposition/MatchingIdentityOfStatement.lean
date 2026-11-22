module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingIdentityOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_identity_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMIdOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchId.matchLMIdOf | exact GlobalTheory.CompanionTheory.MatchId.matchLMIdOf | (intros; apply GlobalTheory.CompanionTheory.MatchId.matchLMIdOf <;> assumption)
