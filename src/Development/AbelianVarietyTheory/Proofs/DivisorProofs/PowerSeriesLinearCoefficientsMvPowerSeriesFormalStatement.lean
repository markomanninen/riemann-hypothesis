module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesLinearCoefficientsMvPowerSeriesFormal
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeriesLinearCoefficients_mvPowerSeriesFormalLog : ∀ (Q : Type) [CommRing Q] [Algebra ℚ Q] (d : ℕ) (g : MvPowerSeries (Fin d) Q), constantCoeff g = 1 → ∀ i, lin (formalLog g) i = lin g i := by
  first | exact @GlobalTheory.FormalCalc.lin_formalLog | exact GlobalTheory.FormalCalc.lin_formalLog | (intros; apply GlobalTheory.FormalCalc.lin_formalLog <;> assumption)
