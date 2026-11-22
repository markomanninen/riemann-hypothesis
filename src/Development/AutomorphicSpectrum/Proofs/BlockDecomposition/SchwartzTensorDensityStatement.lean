module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzTensorDensity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_tensor_density : SchwTensor := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor | exact GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor | (intros; apply GlobalTheory.CompanionTheory.ThTot.SchwT.schwTensor <;> assumption)
