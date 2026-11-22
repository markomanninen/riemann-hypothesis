module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalConvolutionCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CuspDiscreteDecompositionOfTraceClass
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness

@[expose] public section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_convolution_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (f : GA E a → ℂ), Continuous f → HasCompactSupport f → IsCompactOperator (repOp (Rcusp μ) μ f) := by
  first | exact @GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp | exact GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp | (intros; apply GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp <;> assumption)
