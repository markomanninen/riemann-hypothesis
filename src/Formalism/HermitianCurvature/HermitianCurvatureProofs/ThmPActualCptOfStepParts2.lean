module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfOuter
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousExtensionOfFourierDecay

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

def DecayData (n : ℕ) (C : ℝ) (D : ℂ → ℂ) : Prop :=
  Integrable D ∧ Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t) ∧ (∀ t, t ≠ 0 → ContinuousAt D t) ∧
    (∀ s, ‖∫ t, fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))) ∧
    ∀ s, ‖∫ t, fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

section Gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

end Gen

end Formalism.FourierDecayAlt.P5.HerC
