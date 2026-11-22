module

public import Mathlib
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ShiftAtRExistsEq
public import Formalism.HermitianCurvature.FrameExists2
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgMulLeft
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HpkConjTranspose

@[expose] public section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Matrix

namespace GlobalTheory.CompanionTheory.OmegaBiInv

theorem omg_N_mul_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → inWb k r z' → ∀ g ∈ B.GV k r, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, GlobalTheory.WigSh.omg k r z z' (n * g * n') = GlobalTheory.WigSh.omg k r z z' (g) := by
  intro k r z z' hz hz' g hg n hn n' hn'
  rw [Matrix.mul_assoc, GlobalTheory.WigSh.OmLeftN.omg_mul_left k r z z' (g * n') n hz hn]
  exact GlobalTheory.WigSh.omg_mul_N k r z z' g n' hz hz' hg hn'

end GlobalTheory.CompanionTheory.OmegaBiInv
