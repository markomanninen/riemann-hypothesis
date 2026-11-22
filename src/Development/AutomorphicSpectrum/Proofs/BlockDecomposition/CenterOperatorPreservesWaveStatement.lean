module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorPreservesWave
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

@[expose] public section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.center_operator_preserves_wave : RCalc → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V) (w : List (Bool × ℕ)), IsWave E u → IsWave E (fun t => zOp w (u t)) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.WaveZ.isWave_zOp | exact GlobalTheory.CompanionTheory.WaveMult.WaveZ.isWave_zOp | (intros; apply GlobalTheory.CompanionTheory.WaveMult.WaveZ.isWave_zOp <;> assumption)
