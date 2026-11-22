module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInfiniteScaling
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger

@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_infinite_scaling : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (u : κ → ℝ), (∀ j, 0 < u j) →
    ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (f : (κ → AF F) → ℝ≥0∞), ∫⁻ x, f (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) ∂μ =
      (ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F))⁻¹ * ∫⁻ x, f x ∂μ := by
  first | exact @GlobalTheory.TorusTheta.lintegral_infScale_pi | exact GlobalTheory.TorusTheta.lintegral_infScale_pi | (intros; apply GlobalTheory.TorusTheta.lintegral_infScale_pi <;> assumption)
