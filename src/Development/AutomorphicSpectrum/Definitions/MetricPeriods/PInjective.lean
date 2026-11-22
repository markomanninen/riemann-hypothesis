module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LogPeriodsModel

open Matrix Metric GroundTheory.Heights₂.Heights.Regular

theorem P_injective {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : LogPeriods n a g Λ)
    {w : Fin n → ℂ} (hw : w ∈ logCover L.a_le) : Function.Injective (L.P w) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  apply L.unimod.1
  refine LinearMap.ext fun y => ?_
  have := L.im w hw x y
  rw [hx] at this
  simp only [zero_dotProduct, Complex.zero_im] at this
  simp only [map_zero, LinearMap.zero_apply]
  exact_mod_cast this.symm

end GlobalTheory.CompanionTheory.Ar.Flat.LogPeriodsModel
