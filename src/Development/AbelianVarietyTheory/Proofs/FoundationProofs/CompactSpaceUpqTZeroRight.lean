module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCD
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.HaarUpqEqOfOmegaDensity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqDefiniteCompact

@[expose] public section

open Formalism.BasicNotions MeasureTheory Filter Topology

namespace GlobalTheory

theorem compactSpace_UpqT_zero_right : ∀ N : ℕ, CompactSpace (UpqT N 0) :=
  fun N => (GlobalTheory.compactSpace_UpqT_definite N).1

end GlobalTheory
