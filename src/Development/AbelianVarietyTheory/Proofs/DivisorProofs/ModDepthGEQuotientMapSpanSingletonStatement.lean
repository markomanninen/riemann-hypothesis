module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGEQuotientMapSpanSingleton
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree

@[expose] public section

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modDepthGE_quotient_span_of_isSMulRegular : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Finite R A] (f : R), f ∈ maximalIdeal R → ∀ [IsLocalRing (R ⧸ Ideal.span {f})], IsSMulRegular A f → ∀ n : ℕ, ReciprocityTheory.CA.ModDepthGE R A (n + 1) → ReciprocityTheory.CA.ModDepthGE (R ⧸ Ideal.span {f}) (A ⧸ (Ideal.span {f}).map (algebraMap R A)) n := by
  first | exact @GlobalTheory.modDepthGE_quotient_map_span_singleton | exact GlobalTheory.modDepthGE_quotient_map_span_singleton | (intros; apply GlobalTheory.modDepthGE_quotient_map_span_singleton <;> assumption)
