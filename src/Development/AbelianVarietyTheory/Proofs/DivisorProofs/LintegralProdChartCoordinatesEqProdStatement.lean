module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralProdChartCoordinatesEqProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_prod_chartCoordinates_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (h : (Low r → ℂ) → ℝ≥0∞), Measurable h → ∫⁻ z, ∏ τ, h (zOf X z τ) = ∏ _τ : X.Ψ, ∫⁻ w, h w := by
  first | exact @GlobalTheory.IntBall.lintegral_prod_zOf | exact GlobalTheory.IntBall.lintegral_prod_zOf | (intros; apply GlobalTheory.IntBall.lintegral_prod_zOf <;> assumption)
