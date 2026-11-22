module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularPowerTorus
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_power_torus : PositivityTheory.Rg.BcB.F.MLM.RegPowT := by
  first | exact @GlobalTheory.CompanionTheory.RegPow.regPowT | exact GlobalTheory.CompanionTheory.RegPow.regPowT | (intros; apply GlobalTheory.CompanionTheory.RegPow.regPowT <;> assumption)
