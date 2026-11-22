module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealFirstNilpotent
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.MuQMemHarmSet

@[expose] public section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_first_nilpotent : PositivityTheory.RgBcC.RealD.N1 := by
  first | exact @GlobalTheory.CompanionTheory.HarmCone.harm_cone | exact GlobalTheory.CompanionTheory.HarmCone.harm_cone | (intros; apply GlobalTheory.CompanionTheory.HarmCone.harm_cone <;> assumption)
