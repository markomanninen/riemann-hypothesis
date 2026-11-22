module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiscreteValuationCentredCompleteNormal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction

@[expose] public section

open IsLocalRing GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_discreteValuation_centred_completeNormal : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∃ ν : Valuation (FractionRing V) (WithZero (Multiplicative ℤ)), (∀ v : V, ν (algebraMap V (FractionRing V) v) ≤ 1) ∧ ∀ v ∈ maximalIdeal V, ν (algebraMap V (FractionRing V) v) < 1 := by
  first | exact @GlobalTheory.DivVal.exists_valuation_centre | exact GlobalTheory.DivVal.exists_valuation_centre | (intros; apply GlobalTheory.DivVal.exists_valuation_centre <;> assumption)
