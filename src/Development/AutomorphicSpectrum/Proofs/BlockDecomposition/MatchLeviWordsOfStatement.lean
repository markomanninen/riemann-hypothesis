module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLeviWordsOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDetStatement

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.match_levi_words_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordSOf := by
  first | exact @GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | exact GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf | (intros; apply GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf <;> assumption)
