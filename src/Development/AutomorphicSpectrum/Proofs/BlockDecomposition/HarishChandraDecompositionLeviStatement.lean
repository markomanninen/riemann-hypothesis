module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraDecompositionLevi
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction

@[expose] public section

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_decomposition_levi : PositivityTheory.RgBcC.RealD.HCdecLv := by
  first | exact @GlobalTheory.CompanionTheory.RealHCLv.hcdecLv | exact GlobalTheory.CompanionTheory.RealHCLv.hcdecLv | (intros; apply GlobalTheory.CompanionTheory.RealHCLv.hcdecLv <;> assumption)
