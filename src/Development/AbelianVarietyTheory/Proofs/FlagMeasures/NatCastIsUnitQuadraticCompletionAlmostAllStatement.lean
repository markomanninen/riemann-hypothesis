module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NatCastIsUnitQuadraticCompletionAlmostAll
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
theorem _root_.GlobalTheory.T.natCast_isUnit_quadraticCompletion_almost_all : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (N : ℕ), N ≠ 0 → {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = (N : (A.loc p).Fp)}.Finite := by
  first | exact @GlobalTheory.HL.Glue.natCast_isUnit_ae | exact GlobalTheory.HL.Glue.natCast_isUnit_ae | (intros; apply GlobalTheory.HL.Glue.natCast_isUnit_ae <;> assumption)
