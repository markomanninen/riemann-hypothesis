module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.InnerZero

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.compl :
    UpperTheory.V.Af.StrongMultiplicityOne.Compl := by
  intro E _ _ n μ _ U l hs
  have hStable : Fb.Stab (orthRel (CuspidalSpectrum.cuspToL2 μ) (centralCuspForms E n) U) := by
    refine ⟨fun X φ hφ => ?_, fun k φ hφ => ?_, fun g φ hφ => ?_⟩
    · refine map_mem_orthRel (A' := fun y => -(gkModuleCusp E n).ρ X y) (Fb.stab_central.ρ X)
        (fun x hx y hy => ?_) (fun u hu => U.neg_mem (hs.ρ X u hu)) hφ
      rw [map_neg, inner_neg_left, neg_eq_iff_add_eq_zero]
      exact petersson_inner_lieAlgebra_skewAdjoint μ X (l hx) hy
    · refine map_mem_orthRel (A' := (gkModuleCusp E n).σ k⁻¹) (Fb.stab_central.σ k)
        (fun x hx y hy => ?_) (hs.σ k⁻¹) hφ
      have hInv : (gkModuleCusp E n).σ k ((gkModuleCusp E n).σ k⁻¹ x) = x := by
        change ((gkModuleCusp E n).σ k * (gkModuleCusp E n).σ k⁻¹) x = x
        simp only [← map_mul (gkModuleCusp E n).σ k k⁻¹, mul_inv_cancel, map_one,
          one_apply_eq_self]
      exact (petersson_inner_maximalCompact_invariant μ k (l (hs.σ k⁻¹ x hx)) hy).symm.trans
        (congrArg (fun z => inner ℂ (CuspidalSpectrum.cuspToL2 μ z)
          (CuspidalSpectrum.cuspToL2 μ ((gkModuleCusp E n).σ k y))) hInv)
    · refine map_mem_orthRel (A' := finRepCusp E n g⁻¹) (Fb.stab_central.τ g)
        (fun x hx y hy => ?_) (hs.τ g⁻¹) hφ
      have hInv : finRepCusp E n g (finRepCusp E n g⁻¹ x) = x := by
        change (finRepCusp E n g * finRepCusp E n g⁻¹) x = x
        simp only [← map_mul (finRepCusp E n) g g⁻¹, mul_inv_cancel, map_one,
          one_apply_eq_self]
      exact (petersson_inner_finiteAdelic_invariant μ g (l (hs.τ g⁻¹ x hx)) hy).symm.trans
        (congrArg (fun z => inner ℂ (CuspidalSpectrum.cuspToL2 μ z)
          (CuspidalSpectrum.cuspToL2 μ (finRepCusp E n g y))) hInv)
  exact ⟨orthRel (CuspidalSpectrum.cuspToL2 μ) (centralCuspForms E n) U,
    hStable, CuspidalSpectrum.sup_orthRel_centralCuspForms μ U l hs.ρ hs.τ,
    fun φ hφ φ' hφ' => hφ'.2 φ hφ⟩
