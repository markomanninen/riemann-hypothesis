module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.DenseHolds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.CmpForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.QuotMk
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsCuspidalOfConstantTermEqZero
public import GroundTheory.AutomorphicForms.L2LocalComponents

@[expose] public section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem rangeLe_holds : RangeLe := by
  intro E _ _ _ a μ _ μ₁ _ hp v
  have hv : v ∈ ((centralCuspForms E a).map (cuspVecL μ₁)).topologicalClosure := by
    rw [topologicalClosure_map_centralCuspForms μ₁]
    exact Submodule.mem_top
  have hmap : Set.MapsTo (cmp hp) (↑((centralCuspForms E a).map (cuspVecL μ₁)) : Set (CuspL2 μ₁))
      (L2cusp μ : Set (L2 (latticeGL E a) μ)) := by
    rintro _ ⟨φ, hφ, rfl⟩
    have hc : Continuous φ.1 := φ.2.1.continuous
    have hl : IsLeftInvariant φ.1 := φ.2.1.isLeftInvariant
    have hcont : φ.1 ∈ cuspCont E a := by
      refine mem_cuspCont.2 ⟨hc, fun γ g => hl γ g, ?_,
        UpperTheory.isCuspidal_of_constantTerm_eq_zero E a φ.1 hl hc φ.2.2⟩
      intro t g
      rw [splitCentre_comm, splitEq_holds E a t]
      exact apply_mul_centralSection_of_mem hφ _ _
    apply mem_L2cusp_of_ae_eq hcont
    have hrep :
        (toLp μ₁ (cuspVecL μ₁ φ) : RightCosetSpace (Γ1 E a) → ℂ)
          =ᵐ[RightCosetSpace.quotientMeasure (Γ1 E a) μ₁] cuspQuot hl := by
      rw [toLp_cuspVecL]
      exact coeFn_cuspToL2 μ₁ φ
    have hquot :
        (cmp hp (cuspVecL μ₁ φ) : Quot (latticeGL E a) → ℂ)
          =ᵐ[quotMeasure (latticeGL E a) μ] cuspQuot hl ∘ quotMap E a :=
      (Lp.coeFn_compMeasurePreserving _ hp).trans (hp.quasiMeasurePreserving.ae_eq_comp hrep)
    filter_upwards [ae_quotMeasure_iff.1 hquot] with g hg
    calc
      lift (latticeGL E a) (cmp hp (cuspVecL μ₁ φ)) g =
          cuspQuot hl (quotMap E a (mk (latticeGL E a) g)) := hg
      _ = φ.1 g := by
        rw [quotMk_holds E a g, cuspQuot_mk, coe_retractOne, ← (Reduction.centralSection E a).map_inv]
        exact apply_mul_centralSection_of_mem hφ _ _
  exact hmap.closure_left (cmp hp).continuous (isClosed_L2cusp μ) hv

end UpperTheory.V.KernelIndexFullLattice
