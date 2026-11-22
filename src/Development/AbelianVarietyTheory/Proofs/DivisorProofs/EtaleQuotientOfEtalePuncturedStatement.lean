module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleQuotientOfEtalePunctured
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PurityFree

@[expose] public section

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_quotient_of_etale_punctured' : ∀ (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] (f : R) [IsLocalRing (R ⧸ Ideal.span {f})], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ (P : Ideal (R ⧸ Ideal.span {f})) [P.IsPrime], P ≠ maximalIdeal (R ⧸ Ideal.span {f}) → Algebra.Etale (Localization.AtPrime P) (TensorProduct (R ⧸ Ideal.span {f}) (Localization.AtPrime P) (A ⧸ (Ideal.span {f}).map (algebraMap R A))) := by
  first | exact @GlobalTheory.etale_quotient_of_etale_punctured | exact GlobalTheory.etale_quotient_of_etale_punctured | (intros; apply GlobalTheory.etale_quotient_of_etale_punctured <;> assumption)
