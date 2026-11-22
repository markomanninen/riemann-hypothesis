module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.E45FinalGluing
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TreeParts

@[expose] public section

open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.e45_final_gluing : PositivityTheory.Rg.BcB.SpectralAccumulation.InfinitesimalCharacterGlue := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.eFinalGlue | exact GlobalTheory.CompanionTheory.EGlue.eFinalGlue | (intros; apply GlobalTheory.CompanionTheory.EGlue.eFinalGlue <;> assumption)
