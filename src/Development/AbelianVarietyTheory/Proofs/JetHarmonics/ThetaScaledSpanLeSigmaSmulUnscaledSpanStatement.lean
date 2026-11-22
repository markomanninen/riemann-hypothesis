module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaScaledSpanLeSigmaSmulUnscaledSpan
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

@[expose] public section

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.FormTies
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_scaled_span_le_sigma_smul_unscaled_span : ∀ (D : D7) (B : WeightFamilies.Prov D) (P6 : ModuliIntegralCharts.Prov D) (j : ℕ) (X : WeightAlgebra.PJ D B P6 j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ), WeightAlgebra.IsF' ka wL wF T wF.n → ka.n = wF.n + T * wL.n → WeightFamilies.dimY D j ≤ T → sigRec B hinj EX ka wL wF T ≠ 0 ∧ ∀ F ∈ X.Theta (scalOfP B hinj EX p ka wL wF T) ka wL wF T, ∃ G ∈ thetaPlain X ka wL wF T, F = sigRec B hinj EX ka wL wF T • G := by
  first | exact @GlobalTheory.ScaledSpan.theta_le_sigma_smul | exact GlobalTheory.ScaledSpan.theta_le_sigma_smul | (intros; apply GlobalTheory.ScaledSpan.theta_le_sigma_smul <;> assumption)
