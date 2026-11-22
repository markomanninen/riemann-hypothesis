module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularQuotientPrimeElement

@[expose] public section

theorem _root_.GlobalTheory.T.regular_quotient_prime_element : ∀ (A : Type) [CommRing A] [IsDomain A] (P : Ideal A) [P.IsPrime] (x : A), x ≠ 0 → x ∈ P → IsRegularRing (A ⧸ Ideal.span {x}) → Prime (algebraMap A (Localization.AtPrime P) x) := by
  first | exact @_root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient | exact _root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient | (intros; apply _root_.GlobalTheory.prime_algebraMap_localization_of_isRegularRing_quotient <;> assumption)
