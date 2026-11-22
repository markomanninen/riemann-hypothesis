module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemUnitaryGroupIffIsIsometry
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.EqExpFderiv

@[expose] public section

open Filter Topology Asymptotics Complex
open scoped Real ComplexConjugate

namespace GlobalTheory.Doubling

noncomputable section

section Rigidity

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G]

end Rigidity

section Series

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G]

def quadPart (h : E → G) (z : E) : G := (2 : ℂ)⁻¹ • iteratedFDeriv ℂ 2 h 0 fun _ => z

end Series

section Character

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem eq_cexp_fderiv_of_map_add {f : E → ℂ} (hf : DifferentiableAt ℂ f 0) (h0 : f 0 ≠ 0)
    (hm : ∀ x y, f (x + y) = f x * f y) (z : E) : f z = cexp (fderiv ℂ f 0 z) := by
  first
  | exact @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv
  | (apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExpOfFrechetDerivative.eq_exp_fderiv ..)

end Character

section Alternating

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

end Alternating

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]

end Lattice

end

end GlobalTheory.Doubling
