module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.QuotMk

@[expose] public section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace UpperTheory.V.KernelIndexFullLattice

theorem cmpForm_holds : CmpForm := by
  intro E _ _ _ a μ _ μ₁ _ hp φ hφ
  have hRep : (toLp μ₁ (cuspVecL μ₁ φ) : RightCosetSpace (Γ1 E a) → ℂ)
      =ᵐ[RightCosetSpace.quotientMeasure (Γ1 E a) μ₁] cuspQuot φ.2.1.isLeftInvariant := by
    rw [toLp_cuspVecL]
    exact coeFn_cuspToL2 μ₁ φ
  have hQuot : (cmp hp (cuspVecL μ₁ φ) : Quot (latticeGL E a) → ℂ)
      =ᵐ[quotMeasure (latticeGL E a) μ] cuspQuot φ.2.1.isLeftInvariant ∘ quotMap E a :=
    (Lp.coeFn_compMeasurePreserving _ hp).trans (hp.quasiMeasurePreserving.ae_eq_comp hRep)
  filter_upwards [ae_quotMeasure_iff.1 hQuot] with g hg
  calc
    lift (latticeGL E a) (cmp hp (cuspVecL μ₁ φ)) g =
        cuspQuot φ.2.1.isLeftInvariant (quotMap E a (mk (latticeGL E a) g)) := hg
    _ = φ.1 g := by
      rw [quotMk_holds E a g, cuspQuot_mk, coe_retractOne, ← (Reduction.centralSection E a).map_inv]
      exact apply_mul_centralSection_of_mem hφ _ _

end UpperTheory.V.KernelIndexFullLattice
