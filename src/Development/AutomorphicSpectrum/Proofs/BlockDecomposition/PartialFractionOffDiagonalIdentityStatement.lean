module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionOffDiagonalIdentity
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Complexify

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fraction_off_diagonal_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i k, i ≠ k → 1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.pfOrth | exact GlobalTheory.CompanionTheory.RgHeFrame.pfOrth | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.pfOrth <;> assumption)
