module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
public import GroundTheory.AutomorphicForms.GKModules.KernelCalculus
public import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute

@[expose] public section

open MeasureTheory NumberField
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped TensorProduct

namespace UpperTheory.ConvolutionTheory.Dp

attribute [local instance 100] LieRing.ofAssociativeRing

section General

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (π : BanachRep G E)

theorem kernel_uAction (u : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra) (f : h.smoothFuns (F := ℂ))
    (hf : h.IsTestFunction fun g => f.1 g⁻¹) :
    h.IsTestFunction (fun g => (h.rightUAction u f).1 g⁻¹) ∧ ∀ w : E,
      (h.uAction π u ⟨π.integrated μ (fun g => f.1 g⁻¹) w, h.isSmoothVector_integrated π μ hf w⟩ : E) =
        π.integrated μ (fun g => (h.rightUAction u f).1 g⁻¹) w := by
  obtain ⟨t, rfl⟩ : ∃ t, UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra t = u :=
    RingCon.mkₐ_surjective (α := ℝ) (UniversalEnvelopingAlgebra.ringCon ℝ h.lieSubalgebra) u
  induction t using TensorAlgebra.induction generalizing f with
  | algebraMap r =>
    have e : (fun g => (h.rightUAction (UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra (algebraMap ℝ _ r)) f).1 g⁻¹) =
        fun g => (r : ℂ) * f.1 g⁻¹ := by
      rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply]
      rfl
    rw [e]
    refine ⟨IsExpLieAlgebra.IsTestFunction.const_mul hf (r : ℂ), fun w => ?_⟩
    rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, IsExpLieAlgebra.integrated_const_mul_kernel]
    exact (Complex.coe_smul r _).symm
  | ι x =>
    have e : (fun g => (h.rightUAction (UniversalEnvelopingAlgebra.mkAlgHom ℝ h.lieSubalgebra (TensorAlgebra.ι ℝ x)) f).1 g⁻¹) =
        h.convDeriv (h.ofLie x) fun g => f.1 g⁻¹ := by
      show (fun g => (h.rightUAction (UniversalEnvelopingAlgebra.ι ℝ x) f).1 g⁻¹) = _
      rw [IsExpLieAlgebra.rightUAction_ι, IsExpLieAlgebra.coe_rightDerivEnd]
      funext g
      simp only [IsExpLieAlgebra.convDeriv, inv_inv]
    rw [e]
    refine ⟨IsExpLieAlgebra.IsTestFunction.convDeriv hf (h.ofLie x), fun w => ?_⟩
    show (h.uAction π (UniversalEnvelopingAlgebra.ι ℝ x) ⟨_, h.isSmoothVector_integrated π μ hf w⟩ : E) = _
    rw [IsExpLieAlgebra.uAction_ι, IsExpLieAlgebra.coe_derivEnd, h.derivOp_integrated_convDeriv μ π hf]
  | mul a b ha hb =>
    obtain ⟨h1, h2⟩ := hb f hf
    obtain ⟨h3, h4⟩ := ha _ h1
    rw [map_mul, map_mul, map_mul, Module.End.mul_apply]
    refine ⟨h3, fun w => ?_⟩
    rw [Module.End.mul_apply, ← h4 w]
    congr 2
    exact Subtype.ext (h2 w)
  | add a b ha hb =>
    obtain ⟨h1, h2⟩ := hb f hf
    obtain ⟨h3, h4⟩ := ha f hf
    rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply]
    refine ⟨IsExpLieAlgebra.IsTestFunction.add h3 h1, fun w => ?_⟩
    rw [LinearMap.add_apply, Submodule.coe_add, h2, h4]
    exact (h.integrated_add_kernel μ π h3 h1 w).symm

theorem central_map (hπ : ∀ g, ‖π g‖ ≤ 1) {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra} (hz : z ∈ h.centerU) {g : G}
    (hg : g ∈ Subgroup.closure (Set.range h.expG)) : ∀ {v : E} (hv : h.IsSmoothVector π v),
      (h.uAction π z ⟨π g v, h.isSmoothVector_map π hv _⟩ : E) = π g (h.uAction π z ⟨v, hv⟩) := by
  induction hg using Subgroup.closure_induction'' with
  | one => intro v hv; simp only [BanachRep.map_one_apply]
  | mem x hx => obtain ⟨X, rfl⟩ := hx; exact fun hv => h.uAction_map_expG π hπ hz hv X
  | inv_mem x hx => obtain ⟨X, rfl⟩ := hx; rw [← h.expG_neg]; exact fun hv => h.uAction_map_expG π hπ hz hv _
  | mul x y _ _ hx hy =>
    intro v hv
    simp only [BanachRep.map_mul_apply]
    rw [hx (h.isSmoothVector_map π hv y), hy hv]

theorem central_integrated (hπ : ∀ g, ‖π g‖ ≤ 1) (hG : Subgroup.closure (Set.range h.expG) = ⊤)
    {z : UniversalEnvelopingAlgebra ℝ h.lieSubalgebra} (hz : z ∈ h.centerU) {f : G → ℂ} (hf : h.IsTestFunction f) {w : E}
    (hw : h.IsSmoothVector π w) :
    (h.uAction π z ⟨π.integrated μ f w, h.isSmoothVector_integrated π μ hf w⟩ : E) = π.integrated μ f (h.uAction π z ⟨w, hw⟩) := by
  have hListContinuous (D : List 𝔤) : Continuous fun g : G => h.listOp π D (π g w) := by
    simpa only [h.listOp_eq_wordOp π] using
      h.continuous_wordOp_map π hπ hw (fun i : Fin D.length => D[i])
  have hListIntegral (D : List 𝔤) :
      h.listOp π D (π.integrated μ f w) = ∫ g, f g • h.listOp π D (π g w) ∂μ := by
    induction D with
    | nil => rfl
    | cons X D ih =>
      have hSmooth : h.IsSmoothVector π (∫ g, f g • h.listOp π D (π g w) ∂μ) := by
        rw [← ih]
        exact h.isSmoothVector_listOp π (h.isSmoothVector_integrated π μ hf w) D
      rw [h.listOp_cons, ih]
      simpa only [h.listOp_cons] using
        h.derivOp_integral π μ hπ hf (hListContinuous D)
          (fun g => h.isSmoothVector_listOp π (h.isSmoothVector_map π hw g) D) X
          (by simpa only [h.listOp_cons] using hListContinuous (X :: D)) hSmooth
  have hSumContinuous (L : List (ℂ × List 𝔤)) : Continuous fun g : G => h.wordSum π L (π g w) := by
    induction L with
    | nil => simpa only [h.wordSum_nil] using (continuous_const : Continuous fun _ : G => (0 : E))
    | cons p L ih =>
      simpa only [h.wordSum_cons] using ((hListContinuous p.2).fun_const_smul p.1).fun_add ih
  have hSumIntegral (L : List (ℂ × List 𝔤)) :
      h.wordSum π L (π.integrated μ f w) = ∫ g, f g • h.wordSum π L (π g w) ∂μ := by
    have := secondCountableTopology_subgroup_units G
    induction L with
    | nil => simp only [h.wordSum_nil, smul_zero, integral_zero]
    | cons p L ih =>
      have hHead : Integrable (fun g => f g • h.listOp π p.2 (π g w)) μ :=
        ((hf.continuous h).smul (hListContinuous p.2)).integrable_of_hasCompactSupport hf.2.smul_right
      have hTail : Integrable (fun g => f g • h.wordSum π L (π g w)) μ :=
        ((hf.continuous h).smul (hSumContinuous L)).integrable_of_hasCompactSupport hf.2.smul_right
      rw [h.wordSum_cons, ih, hListIntegral p.2, ← integral_smul, ← integral_add (hHead.fun_smul p.1) hTail]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [h.wordSum_cons, smul_add, smul_comm p.1 (f g)]
  obtain ⟨L, hL⟩ := h.exists_wordSum π z
  refine (hL ⟨_, h.isSmoothVector_integrated π μ hf w⟩).trans ((hSumIntegral L).trans ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  exact congrArg (f g • ·) ((hL ⟨π g w, h.isSmoothVector_map π hw _⟩).symm.trans
    (central_map h π hπ hz (hG ▸ Subgroup.mem_top g) hw))

end General

end UpperTheory.ConvolutionTheory.Dp
