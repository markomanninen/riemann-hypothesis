module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDomainFacts
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_domain_facts : PositivityTheory.RgBcC.Fc.DenseD := by
  first | exact @GlobalTheory.CompanionTheory.DenseCpt.denseD | exact GlobalTheory.CompanionTheory.DenseCpt.denseD | (intros; apply GlobalTheory.CompanionTheory.DenseCpt.denseD <;> assumption)
