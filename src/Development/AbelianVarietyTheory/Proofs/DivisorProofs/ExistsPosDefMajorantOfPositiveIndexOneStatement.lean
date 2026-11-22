module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosDefMajorantOfPositiveIndexOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne

@[expose] public section

open Matrix GlobalTheory.LKTrip
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_posDef_majorant_of_positiveIndex_one : ∀ {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian), H.det ≠ 0 → sigPosH hH = 1 → ∀ z : Fin n → ℂ, 0 < (star z ⬝ᵥ H *ᵥ z).re → ∃ P : Matrix (Fin n) (Fin n) ℂ, P.IsHermitian ∧ (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) ∧ ∀ (Y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (c : ℂ), 0 < s → Yᴴ * H * Y = (s : ℂ) • H → Y *ᵥ z = c • z → Yᴴ * P * Y = (s : ℂ) • P := by
  first | (exact @GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one) | (exact GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one) | (intros; apply GlobalTheory.exists_posDef_majorant_of_sigPosH_eq_one  <;> assumption)
