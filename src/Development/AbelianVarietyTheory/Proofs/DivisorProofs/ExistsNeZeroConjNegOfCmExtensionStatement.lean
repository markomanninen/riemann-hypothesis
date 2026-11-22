module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroConjNegOfCmExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_conj_neg_of_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∃ ξ₀ : E, ξ₀ ≠ 0 ∧ σ ξ₀ = -ξ₀ := by
  first | exact @GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg | exact GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg | (intros; apply GlobalTheory.CMTraceZero.exists_ne_zero_conj_neg <;> assumption)
