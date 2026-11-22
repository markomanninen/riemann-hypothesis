module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalGlobalDictionary
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_local_global_dictionary : PositivityTheory.RgEis.DictInf := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.dictInf | exact GlobalTheory.CompanionTheory.RgEis.dictInf | (intros; apply GlobalTheory.CompanionTheory.RgEis.dictInf <;> assumption)
