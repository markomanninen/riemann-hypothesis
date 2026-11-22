module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFiniteSpanningShortGeneratorsSmallSupNorm
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.exists_finite_spanning_short_generators_small_supNorm : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → w.LastPos → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SpanAt (recPJ h j hj) w → ∃ Sh : Finset ((recB h.toLawsCore).Cusp j w), (∀ g ∈ Sh, g ∈ (recPJ h j hj).shortTh w ∧ ∀ σ, Real.log ((recB h.toLawsCore).supN j w σ g) ≤ 400 * Zb D large₂ * w.size) ∧ Submodule.span (recB h.toLawsCore).KO (Sh : Set ((recB h.toLawsCore).Cusp j w)) = ⊤ := by
  exact @GlobalTheory.RunIn.exists_short_family_small
