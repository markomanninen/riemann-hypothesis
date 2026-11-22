module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumIndicatorNonzero
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_indicator_nonzero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∃ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator
        (fun _ => (1 : ℂ)))) ≠ 0 := by
  first | exact @GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero | exact GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero | (intros; apply GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero <;> assumption)
