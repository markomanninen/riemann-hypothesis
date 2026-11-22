module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGeneration
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

@[expose] public section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_generation : SecLaw → TestSph → AvgMem → AvgInv → SideOf → TestK → Core → MirGen := by
  first | exact @GlobalTheory.CompanionTheory.EisMir.mirGen_of_core | exact GlobalTheory.CompanionTheory.EisMir.mirGen_of_core | (intros; apply GlobalTheory.CompanionTheory.EisMir.mirGen_of_core <;> assumption)
