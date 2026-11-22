module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.Published

def LanglandsExhaustionGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (x : IrrGL (k := k)), ∃ 𝔪 : Multiset (Segment k), IsL 𝔪 x.rep

end GlobalTheory.Published

end
