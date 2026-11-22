module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeMassEqFinprodLocal
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianLattice_mass_eq_finprod_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → {p | (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ) ≠ (G.S p).K0}.Finite ∧ G.mu Λ = ∏ᶠ p, (G.S p).mu (A.lat p Λ) := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  exact GlobalTheory.HL.MassProduct.mass_eq_finprod A r k G hk Λ
    (by first | exact hΛ | exact hΛ.toIsLattice)
