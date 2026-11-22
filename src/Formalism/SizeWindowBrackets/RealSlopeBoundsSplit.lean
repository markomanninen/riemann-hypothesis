module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

namespace Formalism.LFunctionChainParameters.WeightedMeanLemmas

open Finset

noncomputable section

def wmean {ι : Type*} [Fintype ι] (d X : ι → ℝ) : ℝ :=
  (∑ u, d u * X u) / ∑ u, d u

def sF {ι : Type*} [Fintype ι] (d muN h : ι → ℝ) : ℝ :=
  wmean d (fun u => muN u - h u)

end

end Formalism.LFunctionChainParameters.WeightedMeanLemmas
