module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMul
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

@[expose] public section

open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counting_bound_alt : CountBd := by
  first | exact @GlobalTheory.CompanionTheory.MassCount.countBd | exact GlobalTheory.CompanionTheory.MassCount.countBd | (intros; apply GlobalTheory.CompanionTheory.MassCount.countBd <;> assumption)
