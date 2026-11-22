module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviStabilityReal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.LeviCommutantWordReduction

@[expose] public section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_stability_real : PositivityTheory.RgBcC.RealD.LevStab := by
  first | exact @GlobalTheory.CompanionTheory.LevBd.levStab | exact GlobalTheory.CompanionTheory.LevBd.levStab | (intros; apply GlobalTheory.CompanionTheory.LevBd.levStab <;> assumption)
