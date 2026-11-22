module

public import Mathlib
public import GroundTheory.PAdicHodge.RobbaSeries
public import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
public import GroundTheory.PAdicHodge.PerfectoidField
public import GroundTheory.PAdicHodge.SlopeCauchyBinet

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent Module

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)]


variable (K) in
def dvUnif : K := ((IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose : K)

theorem irreducible_dvUnif :
    Irreducible (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose :=
  (IsDiscreteValuationRing.exists_irreducible (normInteger K)).choose_spec

theorem norm_eq_one_of_isUnit {z : normInteger K} (hz : IsUnit z) : ‖(z : K)‖ = 1 := by
  have := (normInteger_integers (K := K)).isUnit_iff_valuation_eq_one.1 hz
  rw [NormedField.valuation_apply, ← NNReal.coe_eq_one] at this
  exact this

theorem exists_norm_eq_zpow {x : K} (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = ‖dvUnif K‖ ^ n := by
  have key : ∀ y : K, y ≠ 0 → ‖y‖ ≤ 1 → ∃ n : ℕ, ‖y‖ = ‖dvUnif K‖ ^ n := by
    intro y hy hy1
    let z : normInteger K := ⟨y, mem_normInteger.2 hy1⟩
    have hz : z ≠ 0 := fun h => hy (congrArg Subtype.val h)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz irreducible_dvUnif
    refine ⟨n, ?_⟩
    have h2 := congrArg (fun w : normInteger K => (w : K)) hu
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow] at h2
    rw [show y = (z : K) from rfl, h2, norm_mul, norm_pow, norm_eq_one_of_isUnit u.isUnit, one_mul]
    rfl
  rcases le_total ‖x‖ 1 with h | h
  · obtain ⟨n, hn⟩ := key x hx h
    exact ⟨n, by rw [hn, zpow_natCast]⟩
  · obtain ⟨n, hn⟩ := key x⁻¹ (inv_ne_zero hx) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h)
    refine ⟨-(n : ℤ), ?_⟩
    rw [norm_inv] at hn
    rw [zpow_neg, zpow_natCast, ← hn, inv_inv]

namespace Robba

end Robba

namespace Robba

end Robba

namespace PhiModule

open Matrix

end PhiModule

end GroundTheory.PAdicHodge
