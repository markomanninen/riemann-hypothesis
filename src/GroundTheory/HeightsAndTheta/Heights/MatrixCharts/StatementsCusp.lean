module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

def leadMinor {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (i : ℕ) : ℝ :=
  (Matrix.of fun a b : Fin i =>
    if h : (a : ℕ) < d ∧ (b : ℕ) < d then S ⟨a, h.1⟩ ⟨b, h.2⟩ else 0).det

def periodBasis {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Fin (g + g) → Fin g → ℂ :=
  Fin.append (fun k => Pi.single k 1) (fun k => τ *ᵥ Pi.single k 1)

def periodGram {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin (g + g)) (Fin (g + g)) ℝ :=
  Matrix.of fun i j => hermPair (τ.map Complex.im)⁻¹ (periodBasis τ i) (periodBasis τ j)

end

end GroundTheory.Heights₂.Heights
