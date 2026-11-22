module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient

@[expose] public section

namespace GlobalTheory.Published

def GeometricLemmaFiltration : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.SmGL.JacquetOfInducedFiltration k

end GlobalTheory.Published
