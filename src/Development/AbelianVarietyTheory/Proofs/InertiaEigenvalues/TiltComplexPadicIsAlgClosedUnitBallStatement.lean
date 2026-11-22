module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltComplexPadicIsAlgClosedUnitBall
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
public import GroundTheory.PAdicHodge.TiltField

@[expose] public section

open Formalism.Per GlobalTheory.PSer GroundTheory.PAdicHodge
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tilt_complexPadic_isAlgClosed_unitBall : ∀ (l : ℕ) [Fact l.Prime],
    IsAlgClosed (FractionRing (PreTilt (normInteger ℂ_[l]) l)) ∧
      ∃ ι : Fl l →+* FractionRing (PreTilt (normInteger ℂ_[l]) l),
        (∀ x, tiltSharp ℂ_[l] l (ι x) = sh x) ∧
        (∀ z : FractionRing (PreTilt (normInteger ℂ_[l]) l), ‖z‖ ≤ 1 → ∃ x, ι x = z) :=
  GlobalTheory.PSer.tilt_isAlgClosed_and_unitBall
