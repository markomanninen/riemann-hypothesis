module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSumLeibniz
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarPullbackHolomorphicZero

@[expose] public section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
open Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem dbarAt_congr {n : ℕ} {γ δ : V n → Alt n} {v : V n} (h : γ =ᶠ[𝓝 v] δ) :
    dbarAt γ v = dbarAt δ v := by
  unfold dbarAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  have hS : (fun x => (bas n).repr (γ x) S) =ᶠ[𝓝 v] fun x => (bas n).repr (δ x) S := h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx
  show GlobalTheory.dbar _ v (coordVec a) • _ = GlobalTheory.dbar _ v (coordVec a) • _
  rw [GlobalTheory.dbar_congr hS]

end GlobalTheory.CxForm
