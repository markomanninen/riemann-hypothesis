module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproxStab
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_St_approximating_local_elements : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, (∀ p, n p ∈ (G.S p).St) → {p | n p ∉ (G.S p).K0}.Finite → ∃ g ∈ G.St, ∀ p g', A.Ext p g g' → (n p)⁻¹ * g' ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
  first | exact @GlobalTheory.HL.StrongSt.strong_approx_stab | exact GlobalTheory.HL.StrongSt.strong_approx_stab | (intros; apply GlobalTheory.HL.StrongSt.strong_approx_stab <;> first | assumption | exact (show Submodule.IsFullLattice _ _ from by assumption).toIsLattice)
