module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsMinfOfDensity
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonemptyCompactDualHaarStatement

@[expose] public section

open Formalism.BasicNotions Formalism.IndefR MeasureTheory

namespace GlobalTheory.MinfMeasure

theorem exists_isMinf : ∀ p q : ℕ, ∃ m : Measure (UpqT p q), Lev.IsMinf m :=
  exists_isMinf_of_cd GlobalTheory.T.nonempty_compactDualHaar

end GlobalTheory.MinfMeasure
