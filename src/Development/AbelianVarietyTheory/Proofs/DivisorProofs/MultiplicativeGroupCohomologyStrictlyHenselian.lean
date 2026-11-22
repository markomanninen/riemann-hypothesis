module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroStrictlyHenselianEquivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenseliaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyVanishingOfNoetherianHenselianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialTateTwistCohomologyVanishingIndStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomology

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem GlobalTheory.gm_cohomology_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q) := by
  first
  | exact @_root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology
  | exact _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology
  | (apply _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> assumption)
  | (intros; apply _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology ..)
