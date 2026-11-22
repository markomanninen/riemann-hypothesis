module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInjStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjectiveStatement

@[expose] public section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Published

theorem FontaineBcris.fund_holds (l : ℕ) [Fact l.Prime] (C : Core l) : C.Fund := by
  intro b h1 h2
  exact GlobalTheory.MemLoc.fundamental_exact l C b h1 h2

theorem FontaineBcris_holds : FontaineBcris :=
  FontaineBcris.of_rest fun l _ C =>
    ⟨GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C, FontaineBcris.fund_holds l C, GlobalTheory.MemLoc.FundOnto.fundOnto l C,
      GlobalTheory.T.bcris_regular_of_tensorInj l C (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C)⟩

end GlobalTheory.Published
