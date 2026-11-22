module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary

@[expose] public section

theorem _root_.GlobalTheory.T.siegel_set_unitary : GlobalTheory.Published.SiegelSetUnitary := by
  first | exact @GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary | exact GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary | (intros; apply GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary <;> assumption)
