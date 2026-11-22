module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeBetweenScaledStandardLattices
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemSpanSingleIff

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_between_scaled_standard_lattices : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (p : HeightOneSpectrum (𝓞 F)) (n : ℕ) (Λ : Submodule (A.L p).O (Fin n → (A.loc p).Ep)), IsLat (A.L p) Λ → (∀ y : (A.loc p).Ep, ∃ m : ℕ, m ≠ 0 ∧ (m : (A.loc p).Ep) * y ∈ (A.L p).O) → ∃ m : ℕ, m ≠ 0 ∧ (∀ v : Fin n → (A.loc p).Ep, (∀ i, v i ∈ (A.L p).O) → (m : (A.loc p).Ep) • v ∈ Λ) ∧ ∀ v ∈ Λ, ∀ i, (m : (A.loc p).Ep) * v i ∈ (A.L p).O := by
  first | exact @GlobalTheory.HL.Glue.lat_between | exact GlobalTheory.HL.Glue.lat_between | (intros; apply GlobalTheory.HL.Glue.lat_between <;> assumption)
