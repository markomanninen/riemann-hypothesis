module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitDictionaryHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupEig

@[expose] public section

open PositivityTheory.Rg.BcB.F.Eig
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_dictionary_holds : SplitDict := by
  first | exact @GlobalTheory.CompanionTheory.SplitPlace.splitDict | exact GlobalTheory.CompanionTheory.SplitPlace.splitDict | (intros; apply GlobalTheory.CompanionTheory.SplitPlace.splitDict <;> assumption)
