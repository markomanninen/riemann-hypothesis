module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
public import Formalism.HarderNarasimhan.Statement
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem exists_isConjAt_of_embedding (K : Type) [Field K] [NumberField K] [StarRing K]
    (h : ∃ σ : K →+* ℂ, ∀ x : K, σ (star x) = starRingEnd ℂ (σ x)) :
    ∃ v0 : InfinitePlace K, IsConjAt v0 := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨InfinitePlace.mk σ, fun a => ?_⟩
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rw [e]; exact hσ a
  · rw [e]
    simp only [ComplexEmbedding.conjugate_coe_eq]
    rw [hσ a]

theorem isConjAt_exists_main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K],
    (∃ σ : K →+* ℂ, ∀ x : K, σ (star x) = starRingEnd ℂ (σ x)) →
      ∃ v0 : InfinitePlace K, IsConjAt v0 :=
  fun K _ _ _ h => exists_isConjAt_of_embedding K h

end GlobalTheory
