module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.IsotypQuot

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Pp

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm in
theorem UpperTheory.ConvolutionTheory.R2.Pp.cuspZero :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], UpperTheory.ConvolutionTheory.R2.Pp.CuspZero F := by
  intro F _ _ _ π f hf
  have hc : Continuous f.1 := by
    have hp : Continuous (TR.pInf F) := by
      have hc : Continuous (TR.infEq F).symm :=
        continuous_pi fun w =>
          (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
      exact hc.comp continuous_fst
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hm : Continuous fun x : GA F 2 => g⁻¹ * x := continuous_const.mul continuous_id
    have hI : Continuous (Matrix.GeneralLinearGroup.map (TR.pInf F) : GA F 2 → GL (Fin 2) (TR.Rinf F)) :=
      Continuous.units_map _ (continuous_id.matrix_map hp)
    have hFn : Continuous (Matrix.GeneralLinearGroup.map (pFin F) : GA F 2 → GL (Fin 2) (Af F)) :=
      Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
    have h1 : Continuous fun x : GA F 2 => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val :=
      (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (TR.Rinf F))).comp (hI.comp hm)
    have h2 : ContinuousAt (fun x : GA F 2 => TR.chart f.1 g (TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)) g :=
      ContinuousAt.comp (f := fun x : GA F 2 => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)
        (TR.contDiffAt_chart f.2 g (TR.val_mem_invSet _)).continuousAt h1.continuousAt
    refine h2.congr ?_
    have h3 : {x : GA F 2 | TR.finRep F 2 (Matrix.GeneralLinearGroup.map (pFin F) (g⁻¹ * x)) f = f} ∈ 𝓝 g :=
      ((π.cusp f hf).1.level.preimage (hFn.comp hm)).mem_nhds (by simp)
    filter_upwards [h3] with x hx
    rw [TR.chart_val]
    conv_lhs => rw [← hx]
    change f.1 (g * TR.infGL F 2 _ * finGL F 2 _) = _
    rw [mul_assoc, TR.infGL_mul_finGL, mul_inv_cancel_left]
  refine ⟨⟨hc, (π.cusp f hf).1.left⟩, fun g => ?_⟩
  letI : Unique (BlockIx 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
  rw [← int_one (ι := BlockIx 2 1)]
  have hz := (π.cusp f hf).2 1 one_pos one_lt_two (FourierWhittaker.vecMeasure F (BlockIx 2 1)) (FourierWhittaker.vecDomain F (BlockIx 2 1)) inferInstance (by exact FourierWhittaker.isAddFundamentalDomain_vecDomain) g
  rw [← hz]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have : gl (nU (x default)) = unip x := by
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vn, unip, nilM]
    rfl
  simp only [this]
