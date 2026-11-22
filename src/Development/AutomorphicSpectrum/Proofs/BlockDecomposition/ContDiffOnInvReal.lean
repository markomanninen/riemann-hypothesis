module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolRightHolEq

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Frame

variable {n : ℕ}

theorem contDiffOn_inv_real : ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹) (GLs n) :=
  ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_inv_det_ne_zero.restrict_scalars ℝ

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end GlobalTheory.CompanionTheory.WaveCp.Rep.Frame

namespace GlobalTheory.CompanionTheory.WaveCp.Rep

end GlobalTheory.CompanionTheory.WaveCp.Rep
