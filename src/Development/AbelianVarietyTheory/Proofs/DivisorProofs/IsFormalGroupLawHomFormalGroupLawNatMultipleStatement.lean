module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormalGroupLawHomFormalGroupLawNatMultiple
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFormalGroupLawHom_formalGroupLawNatMultiple : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ n, IsHom μ μ (nmul μ n) := by
  first | exact @GlobalTheory.NMulHom.isHom_nmul | exact GlobalTheory.NMulHom.isHom_nmul | (intros; apply GlobalTheory.NMulHom.isHom_nmul <;> assumption)
