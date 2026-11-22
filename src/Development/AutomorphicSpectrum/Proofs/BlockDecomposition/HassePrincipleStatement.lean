module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrinciple
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

@[expose] public section

open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasse_principle : Hasse := by
  first | exact @GlobalTheory.CompanionTheory.SW.MassHasse.hasse | exact GlobalTheory.CompanionTheory.SW.MassHasse.hasse | (intros; apply GlobalTheory.CompanionTheory.SW.MassHasse.hasse <;> assumption)
