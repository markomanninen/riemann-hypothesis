module

public import Mathlib
public import GroundTheory.PAdicHodge.PerfectoidField
public import GroundTheory.PAdicHodge.TiltValuation
public import GroundTheory.PAdicHodge.TiltField
public import GroundTheory.PAdicHodge.KerTheta
public import GroundTheory.PAdicHodge.TiltMap

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

section Functor

variable {K L M : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField L] [IsUltrametricDist L] [NontriviallyNormedField M] [IsUltrametricDist M]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField L p]
  [IsPerfectoidField M p]
omit [IsUltrametricDist K] [IsUltrametricDist L] [IsUltrametricDist M] in
theorem norm_comp_eq {φ : K →+* L} (hφ : ∀ x, ‖φ x‖ = ‖x‖) {ψ : L →+* M}
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (x : K) : ‖(ψ.comp φ) x‖ = ‖x‖ := by
  rw [RingHom.comp_apply, hψ, hφ]

variable (φ : K →+* L) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (ψ : L →+* M) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)

theorem preTiltMap_comp :
    preTiltMap (p := p) (ψ.comp φ) (norm_comp_eq hφ hψ) =
      (preTiltMap (p := p) ψ hψ).comp (preTiltMap (p := p) φ hφ) := by
  refine RingHom.ext fun x => Perfection.ext fun n => ?_
  rw [RingHom.comp_apply, coeff_preTiltMap, coeff_preTiltMap, coeff_preTiltMap]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (Perfection.coeff (ModP (normInteger K) p) p n x)
  rw [← ha, modPMap_mk, modPMap_mk, modPMap_mk]
  rfl

end Functor

section Density

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]


end Density

section Algebra

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

end Algebra

section IntermediateField

variable {K C : Type*} [NontriviallyNormedField K] [NormedField C] [NormedAlgebra K C]

end IntermediateField

section TiltIntermediate

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

variable (F : IntermediateField K C) [IsPerfectoidField F p]




end TiltIntermediate

end GroundTheory.PAdicHodge
