module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerSplittingDefectEqOfPowEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonSecOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerSplittingDefect_eq_of_pow_eq : ∀ (q : ℕ) [NeZero q] (κ : twZ q ⟶ Gm), (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (u : (Γ(U, ⊤))ˣ), (u : Γ(U, ⊤)) = ζ.1 → Sec.map κ (show Sec (twZ q) U from twGen 1 ζ) = unitSec u) → ∀ (φ : Gm ⟶ (res ℤ (twZ q)).X 0), κ ≫ φ = resι ℤ (twZ q) → ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → ∀ v v' : (Γ(U, ⊤))ˣ, v ^ q = v' ^ q → dv q φ U v = dv q φ U v' := by
  first
  | exact @GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq
  | exact GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq
  | (intros; apply GlobalTheory.EtC.KumPic.dv_eq_of_pow_eq <;> assumption)
