module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantMultiplierGood
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_multiplier_good : PositivityTheory.RgEis.StdGood → PositivityTheory.RgEis.Dict → PositivityTheory.RgEis.DictInf → PositivityTheory.RgEis.CMGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCM.cmGood | exact GlobalTheory.CompanionTheory.RgEisCM.cmGood | (intros; apply GlobalTheory.CompanionTheory.RgEisCM.cmGood <;> assumption)
