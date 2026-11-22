module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentatives
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_coset_representatives : Ad3.R.C0 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant | exact GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant | (intros; apply GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant <;> assumption)
