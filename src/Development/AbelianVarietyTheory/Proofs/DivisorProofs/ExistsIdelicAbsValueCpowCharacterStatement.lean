module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdelicAbsValueCpowCharacter
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idelic_absValue_cpow_character : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (z : ℂ), ∃ χ : HChar E, (∀ (a : ℕ) (φ : Sm E a), zc E a (mulChi a χ φ) = mulChi a χ (zc E a φ + (a * (Module.finrank ℚ E : ℂ) * z) • φ)) ∧ (∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) ∧ (∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ = ‖(((nu E z.re).1 x : ℂˣ) : ℂ)‖) ∧ (z.im = 0 → χ = nu E z.re) := by
  first | exact @GlobalTheory.ResW.exists_abs_cpow | exact GlobalTheory.ResW.exists_abs_cpow | (intros; apply GlobalTheory.ResW.exists_abs_cpow <;> assumption)
