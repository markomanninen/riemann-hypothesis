module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.IsCond

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem

theorem Base.fields_isCond : ∀ (B : Base) (X : PreX B.toPre), B.fields.IsCond (B.primes X).cond := by
  intro B X j
  exact UpperTheory.Ram.isCond_condN B.host j

end GlobalTheory.Mem
