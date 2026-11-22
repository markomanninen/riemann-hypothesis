module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCommonDenominatorForHermitianLatticeData
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToLePerp
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_denominator_for_hermitian_lattice_data : ∀ {E : Type} [Field E] [NumberField E] {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ] (v : ι → E) (g : κ → Fin n → E) (Hm : Matrix (Fin n) (Fin n) E) (sg : E →+* E) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E Λ → ∃ D : ℤ, D ≠ 0 ∧ (∀ i, ∃ o : 𝓞 E, (D : E) * v i = o) ∧ (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * Hm a b * sg (g l b) = o) ∧ ∀ l, (D : 𝓞 E) • g l ∈ Λ := by
  exact @GlobalTheory.DenClear.den_clear
