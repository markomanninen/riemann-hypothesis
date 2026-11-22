module

public import Mathlib
public import Formalism.PeriodIntegrals.DSInfCharCap
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.StatementB
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviFactorInverseModulusProperties

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.FlagMeas GlobalTheory.RealInd

noncomputable section

namespace GlobalTheory.SplitTorus

variable {n : ℕ} (ε : Fin n → Bool)

def bJ (u y : Fin n → ℂ) : ℂ := star u ⬝ᵥ (Jm ε *ᵥ y)

variable {ε}

theorem coord {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (b : Fin n) (y : Fin n → ℂ) :
    bJ ε (P *ᵥ Pi.single b 1) y = ((Pᴴ * Jm ε * P) *ᵥ (P⁻¹ *ᵥ y)) b := by
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).1 hP)
  conv_lhs => rw [show y = P *ᵥ (P⁻¹ *ᵥ y) by rw [mulVec_mulVec, hPP, one_mulVec]]
  rw [bJ, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]
  simp [Pi.star_def, Pi.single_apply, dotProduct]

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
include hP hpq hG

end

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) {p q : Fin n} (hpq : p ≠ q)
    (hG : ∀ a b, (a = p ∨ a = q ∨ b = p ∨ b = q) →
      (Pᴴ * Jm ε * P) a b = if (a = p ∧ b = q) ∨ (a = q ∧ b = p) then 1 else 0)
include hP hpq hG

end

end GlobalTheory.SplitTorus

namespace GlobalTheory.SplitTorus

variable {n : ℕ} {ε : Fin n → Bool}

end GlobalTheory.SplitTorus

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
