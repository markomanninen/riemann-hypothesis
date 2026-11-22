module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegralVanishingOfFibreIntegrals
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_integral_vanishing_of_fibre_integrals : WeilVanish := by
  first | exact @GlobalTheory.Dec.weilVanish | exact GlobalTheory.Dec.weilVanish | (intros; apply GlobalTheory.Dec.weilVanish <;> assumption)
