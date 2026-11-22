module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectEqOfPowEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrFamAddTwo
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistAltI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrictionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKummerTorsorSplittingKummerTorsorSplittingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistReductionResolutionMapGeneratorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) → v ^ Q = w ^ Q → GlobalTheory.EtC.RedChern.defect Q q U v = GlobalTheory.EtC.RedChern.defect Q q U w := by
  first
  | exact @GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq
  | exact GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq
  | (intros; apply GlobalTheory.EtC.RedChern.defect_eq_of_pow_eq <;> assumption)
