module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightDerivativeRightConvolutionEqTestFunction
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcGASmoothAndRderMem
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousSetIntegralConstTermOn

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.right_derivative_rightConvolution_eq_test_function : ∀ {D : D7} {V : HSp D} (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ {f : GA D V → ℂ}, f ∈ GlobalTheory.Orb.CcGA V → ∀ {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}, X ∈ lieAt V τ → ∃ f' ∈ GlobalTheory.Orb.CcGA V, tsupport f' ⊆ tsupport f ∧ ∀ F : GlobalTheory.AutomorphicL2Unitary.DividedPowerChartLift V μ, Rder θ V τ X (GlobalTheory.AutomorphicL2Unitary.convR μ f (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F)) = GlobalTheory.AutomorphicL2Unitary.convR μ f' (GlobalTheory.AutomorphicL2Unitary.lift (GQ V) F) := by
  first | exact @GlobalTheory.ConvRDeriv.Rder_convR | exact GlobalTheory.ConvRDeriv.Rder_convR | (intros; apply GlobalTheory.ConvRDeriv.Rder_convR <;> assumption)
