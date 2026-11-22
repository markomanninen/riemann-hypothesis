module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact

@[expose] public section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.OmegaLebExists

theorem J_conjTranspose (P Q : ℕ) : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  unfold Formalism.UG.Jpq
  rw [fromBlocks_conjTranspose]
  simp

end GlobalTheory.OmegaLebExists
