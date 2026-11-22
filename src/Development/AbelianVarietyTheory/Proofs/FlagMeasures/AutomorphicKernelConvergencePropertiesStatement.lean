module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicKernelConvergenceProperties
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphicKernel_convergence_properties : KernelA := by
  first | exact @GlobalTheory.KernelConv.kernelA | exact GlobalTheory.KernelConv.kernelA | (intros; apply GlobalTheory.KernelConv.kernelA <;> assumption)
