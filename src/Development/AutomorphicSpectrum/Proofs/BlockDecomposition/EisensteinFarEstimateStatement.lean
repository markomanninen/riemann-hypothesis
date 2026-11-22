module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinFarEstimate
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU

@[expose] public section

open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_far_estimate : EFar := by
  first | exact @GlobalTheory.CompanionTheory.FarSeries.eFar | exact GlobalTheory.CompanionTheory.FarSeries.eFar | (intros; apply GlobalTheory.CompanionTheory.FarSeries.eFar <;> assumption)
