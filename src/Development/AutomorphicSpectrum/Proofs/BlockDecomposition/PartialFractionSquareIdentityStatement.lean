module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionSquareIdentity
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Complexify

@[expose] public section

open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fraction_square_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i, 1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2 = pfD d d' i := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.pfDer | exact GlobalTheory.CompanionTheory.RgHeFrame.pfDer | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.pfDer <;> assumption)
