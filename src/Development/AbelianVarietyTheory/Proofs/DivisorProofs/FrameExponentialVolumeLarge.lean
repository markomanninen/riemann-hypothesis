module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
public import Development.AutomorphicArithmetic.LocalEmbeddings.ThinCover
public import Development.AutomorphicArithmetic.LocalEmbeddings.ThinCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaBoundLengthUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightAntitoneBoundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientWeightGapBounds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetNumberQuotientBounds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfPrincipalAndSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndex
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasUnramifiedIntegralFramedPointsOfGoodPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionInverseRootTwistingSectionSpreadStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

namespace GlobalTheory.ThinBerg

open MeasureTheory
open scoped ENNReal

theorem pnorm_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  unfold Data.pnorm
  exact mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _)

theorem le_bergOn_of_ratio {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r)
    {D : D7} (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (hd : ∀ g, (dict g).2 ∈ (U.X (dict g).1).dom)
    (Z : Comp Xo c) (G : WTZ E) (y : FPt U.X) (P : FDSec U.X) (hP : P ∈ holSub U.X (modelWt U G)) {e : ℝ}
    (he : 0 < e) (hy : 0 < ptN (modelWt U G) P ⟨y.1, y.2.1⟩)
    (hb : ∀ z : FPt U.X, e * ptN (modelWt U G) P ⟨z.1, z.2.1⟩ ≤ ptN (modelWt U G) P ⟨y.1, y.2.1⟩) :
    ENNReal.ofReal (e ^ 2) ≤ bergOn U V dict Z G y := by
  set A : ℝ≥0∞ := ENNReal.ofReal (ptN (modelWt U G) P ⟨y.1, y.2.1⟩) with hA
  have hA0 : A ≠ 0 := by rw [hA]; exact (ENNReal.ofReal_pos.2 hy).ne'
  have hsup : supE U.X (modelWt U G) P ≤ ENNReal.ofReal e⁻¹ * A := by
    unfold supE
    refine iSup_le fun z => ?_
    rw [hA, ← ENNReal.ofReal_mul (inv_nonneg.2 he.le)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := hb z
    rw [le_inv_mul_iff₀ he]
    exact h
  have hpet : petE V dict (muOn U V dict Z) (modelWt U G) P ≤ ENNReal.ofReal e⁻¹ * A :=
    (petE_le_supE V dict _ (muPart_univ_le V dict _) hd _ P).trans hsup
  unfold bergOn bergE
  refine le_trans ?_ (le_iSup₂_of_le P hP le_rfl)
  rw [ENNReal.le_div_iff_mul_le (Or.inr (pow_ne_zero 2 hA0)) (Or.inr (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))]
  calc ENNReal.ofReal (e ^ 2) * petE V dict (muOn U V dict Z) (modelWt U G) P ^ 2
      ≤ ENNReal.ofReal (e ^ 2) * (ENNReal.ofReal e⁻¹ * A) ^ 2 := by gcongr
    _ = ENNReal.ofReal (e ^ 2 * e⁻¹ ^ 2) * A ^ 2 := by
        rw [mul_pow, ← mul_assoc, ENNReal.ofReal_mul (sq_nonneg e), ENNReal.ofReal_pow (inv_nonneg.2 he.le)]
    _ = A ^ 2 := by
        rw [← mul_pow, mul_inv_cancel₀ he.ne', one_pow, ENNReal.ofReal_one, one_mul]

end GlobalTheory.ThinBerg

namespace GlobalTheory.ThinBerg

open MeasureTheory

end GlobalTheory.ThinBerg
