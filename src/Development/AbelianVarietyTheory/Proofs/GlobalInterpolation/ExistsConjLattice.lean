module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SmulCommClassGalIntegers
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TendstoCoeffZero

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMRam

open WeierstrassCurve

theorem exists_conj_lattice (σ : ℂ ≃+* ℂ) (L : PeriodPair) :
    ∃ L' : PeriodPair, L'.g₂ = σ L.g₂ ∧ L'.g₃ = σ L.g₃ := by
  first
  | exact @_root_.GlobalTheory.DiscUniformisation.main
  | exact _root_.GlobalTheory.DiscUniformisation.main
  | (apply _root_.GlobalTheory.DiscUniformisation.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.DiscUniformisation.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DiscUniformisation.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DiscUniformisation.main ..)

end GlobalTheory.CMRam
