module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
public import Formalism.LocalToGlobal.Columns.BaseLemmas

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

namespace GlobalTheory.Mem

theorem wts_ok_and_sizes :
    ∀ (B : Base) (X : PreX B.toPre), B.wts.Ok ∧ Sizes (B.primes X) B.wts X.a :=
  fun B X => ⟨B.wts_isOk, B.primes_sizes X⟩

end GlobalTheory.Mem
