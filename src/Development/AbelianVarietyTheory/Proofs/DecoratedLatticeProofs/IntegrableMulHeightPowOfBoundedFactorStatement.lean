module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMulHeightPowOfBoundedFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMatrixCoeffFockVectorsLeDoublingHeightPowStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerFockProductEqProdRealPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralRealUnitaryHaarEqProdUpqHaarStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightAtRealPlaceContinuousPosLeOneStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepWeilDatumNonzeroFockVacuumStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_mul_heightPow_of_bounded_factor : ∀ {G : Type} [MeasurableSpace G] [TopologicalSpace G] [OpensMeasurableSpace G] (μ : Measure G) (z m : G → ℂ) (H : G → ℝ) (C : ℝ) (b t : ℕ), Integrable z μ → Integrable m μ → Continuous H → (∀ g, 0 < H g ∧ H g ≤ 1) → t ≤ b → (∀ g, ‖z g‖ ≤ C * H g ^ ((b : ℝ) / 2) * ‖m g‖) → Integrable (fun g => z g * ((H g : ℝ) : ℂ) ^ (((0 : ℝ) : ℂ) - (t : ℂ) / 2)) μ := by
  first | exact @GlobalTheory.realZeta_integrable_mul_heightPow | exact GlobalTheory.realZeta_integrable_mul_heightPow | (intros; apply GlobalTheory.realZeta_integrable_mul_heightPow <;> assumption)
