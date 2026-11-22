module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand

@[expose] public section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet Matrix

namespace GlobalTheory.GodementJacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isLocallyConstant_char_det {n : Type} [Fintype n] [DecidableEq n] {μ : kˣ →* ℂˣ}
    (hμ : IsSmoothChar μ) :
    IsLocallyConstant fun g : GL n k => ((μ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) := by
  set χ : GL n k →* ℂˣ := μ.comp GeneralLinearGroup.det with hχd
  have hχ : IsOpen (χ.ker : Set (GL n k)) := hμ.preimage GeneralLinearGroup.continuous_det
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (χ.ker : Set (GL n k)) ∈ nhds g0 :=
    (hχ.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have hg' : χ (g0⁻¹ * g) = 1 := hg
  have e : χ g = χ g0 := by
    have := congrArg (χ g0 * ·) hg'
    simp only [← map_mul, mul_inv_cancel_left, mul_one] at this
    exact this
  exact congrArg (fun u : ℂˣ => (u : ℂ)) e

end GlobalTheory.GodementJacquet
