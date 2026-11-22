module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.Assemble
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.SplitEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConstantTermEqZeroOfIsCuspidal

@[expose] public section

open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC GlobalTheory.DiscSpec
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

theorem contMem_holds : ContMem := by
  intro E _ _ _ a μ _ μ₁ _ hp φ hφ h
  obtain ⟨hc, hl, hz, hcu⟩ := mem_cuspCont.1 hφ
  have hL : IsLeftInvariant φ := fun γ g => hl γ g
  have hcusp : AutomorphicForm.IsCuspidal φ := UpperTheory.constantTerm_eq_zero_of_isCuspidal E a φ hL hc hcu
  have hr : ∀ g : GA E a, φ (retractOne g : G1 E a) = φ g := fun g => by
    obtain ⟨t, ht⟩ := exists_split (E := E) (a := a) splitEq_holds (Reduction.detModule E a g)
    have h1 := hz t (retractOne g : G1 E a)
    rw [← h1, splitCentre_comm, coe_retractOne, ← ht, inv_mul_cancel_right]
  have hΦ : cuspQuot hL ∘ quotMap E a = descend (latticeGL E a) φ := by
    funext q
    change cuspQuot hL (RightCosetSpace.mk (Γ1 E a) (retractOne q.out)) = φ q.out
    rw [cuspQuot_mk]
    exact hr q.out
  have hm : MemLp (cuspQuot hL) 2 (RightCosetSpace.quotientMeasure (Γ1 E a) μ₁) := by
    have hs := (continuous_cuspQuot hL hc).aestronglyMeasurable
      (μ := Measure.map (quotMap E a) (quotMeasure (latticeGL E a) μ))
    rw [← hp.map_eq, memLp_map_measure_iff hs hp.aemeasurable, hΦ]
    exact h.2
  have hv : hm.toLp _ ∈ cuspidalL2 μ₁ := by
    change IsCuspidalL2 μ₁ (hm.toLp _)
    intro r h0 h1
    filter_upwards [ae_ctFun_congr μ₁ r (MemLp.coeFn_toLp hm)] with y hy
    rw [constantTermL2, hy]
    simpa only [ctFun, cuspQuot_mk, Subgroup.coe_mul, coe_unipOne, constantTerm, Pi.zero_apply]
      using hcusp r h0 h1 y
  refine ⟨⟨hm.toLp _, hv⟩, Lp.ext ?_⟩
  have hQuot : (cmp hp ⟨hm.toLp _, hv⟩ : Quot (latticeGL E a) → ℂ)
      =ᵐ[quotMeasure (latticeGL E a) μ] cuspQuot hL ∘ quotMap E a :=
    (Lp.coeFn_compMeasurePreserving _ hp).trans
      (hp.quasiMeasurePreserving.ae_eq_comp (MemLp.coeFn_toLp hm))
  rw [hΦ] at hQuot
  exact hQuot.trans h.coeFn_toL2.symm

end UpperTheory.V.KernelIndexFullLattice
