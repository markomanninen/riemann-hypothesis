module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMajorant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant

@[expose] public section

open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbit_majorant : OrbitMaj := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.orbitMaj | exact GlobalTheory.CompanionTheory.ThTot.orbitMaj | (intros; apply GlobalTheory.CompanionTheory.ThTot.orbitMaj <;> assumption)
