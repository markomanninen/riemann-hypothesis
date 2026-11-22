module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsFiniteDimensional
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge

@[expose] public section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.cusp_forms_finite_dimensional : GlobalTheory.UCls.MassBound → GlobalTheory.UCls.TorusBound → ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cuspW Xo c U (wtZ a n)) ∧ (Module.finrank c.F (cuspW Xo c U (wtZ a n)) : ℝ) ≤ supConst D.host.E D.R.r D.host.d l.M (((absA Dw a : ℕ) : ℝ) + ((fdeg D.host.E * D.R.r * n : ℕ) : ℝ) + 1) := by
  exact _root_.GlobalTheory.LevGeo.RankBd.finrank_cuspW_le
