module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCommonStabiliserEqOneOfFixesSecondFrame
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalCommonStabiliser_eq_one_of_fixes_second_frame : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ x ∈ G.St, (∀ b, x (G.f' b) = G.f' b) → x = 1 := by
  first | exact @GlobalTheory.HL.StabFix.eq_one_of_fix | exact GlobalTheory.HL.StabFix.eq_one_of_fix | (intros; apply GlobalTheory.HL.StabFix.eq_one_of_fix <;> assumption)
