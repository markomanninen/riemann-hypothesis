module

public import Formalism.PeriodIntegrals.IsLowUnitH

@[expose] public section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace PI

open PI.UpqRep

section

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsCWCont {Wp : Type*} [NormedAddCommGroup Wp]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (B : H → Wp) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))),
    (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ smoothVecs (k := k) (r := r) σ, ‖B v‖ ≤ C * (Ws.map fun w => ‖dsigW σ w v‖).sum

def thetaH (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  -(Hpk k r * Xᴴ * Hpk k r)

def dsigC (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : H) : H :=
  dsig (k := k) (r := r) σ ((1 / 2 : ℂ) • (X + thetaH k r X)) v +
    Complex.I • dsig (k := k) (r := r) σ ((-(Complex.I / 2)) • (X - thetaH k r X)) v

end

end PI
