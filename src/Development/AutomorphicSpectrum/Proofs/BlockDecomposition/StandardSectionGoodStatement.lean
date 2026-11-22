module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardSectionGood
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_section_good : PositivityTheory.RgEis.StdGood := by
  first | exact @GlobalTheory.CompanionTheory.StdGoodAd.stdGood | exact GlobalTheory.CompanionTheory.StdGoodAd.stdGood | (intros; apply GlobalTheory.CompanionTheory.StdGoodAd.stdGood <;> assumption)
