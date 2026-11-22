module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeCoefficientsOfPadicIntLattices
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bhattScholze_coefficients_of_padicInt_lattices : GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.BhattScholzeCrystallineLattices := by
  first | exact @GlobalTheory.bhattScholze_coeff | exact GlobalTheory.bhattScholze_coeff | (intros; apply GlobalTheory.bhattScholze_coeff <;> assumption)
