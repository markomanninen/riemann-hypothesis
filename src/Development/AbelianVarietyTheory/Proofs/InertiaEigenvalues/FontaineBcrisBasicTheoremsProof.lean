module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjectiveStatement

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem fontaineBcris_of_tensorInj
    (h : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj) : GlobalTheory.Published.FontaineBcris :=
  GlobalTheory.Published.FontaineBcris.of_rest fun l _ C =>
    ⟨h l C, fun b h1 h2 => GlobalTheory.MemLoc.fundamental_exact l C b h1 h2,
      GlobalTheory.MemLoc.FundOnto.fundOnto l C, GlobalTheory.MemLoc.regular_of_tensorInj l C (h l C)⟩

theorem fontaineBcris : GlobalTheory.Published.FontaineBcris :=
  fontaineBcris_of_tensorInj GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective

end GlobalTheory.MemLoc
