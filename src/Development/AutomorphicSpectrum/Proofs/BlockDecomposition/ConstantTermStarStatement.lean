module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermStar
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedMatrixIntegralCompLinearEquivDetStatement

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_star : PositivityTheory.Rg.BcB.F.MLM.CtStar := by
  first | exact @GlobalTheory.CompanionTheory.CtAdj.ctStar | exact GlobalTheory.CompanionTheory.CtAdj.ctStar | (intros; apply GlobalTheory.CompanionTheory.CtAdj.ctStar <;> assumption)
