module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalConvolutionOrthogonalProjectorProof
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalConvolutionOrthogonalProjector_proof : GlobalProj := by
  first | exact @GlobalTheory.GlobProj.globalProj_holds | exact GlobalTheory.GlobProj.globalProj_holds | (intros; apply GlobalTheory.GlobProj.globalProj_holds <;> assumption)
