module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusWithSignUniformisationFrame
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCAlpha
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaValCSteps
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ThetaWeightBounds
public import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusWithSign_uniformisationFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x), ∃ A : I2.TorusAt (U.X k) x.1, A.w0 = H.w0 := by
  first | exact @GlobalTheory.TorusSign.exists_torusAt_w0_eq | exact GlobalTheory.TorusSign.exists_torusAt_w0_eq | (intros; apply GlobalTheory.TorusSign.exists_torusAt_w0_eq <;> assumption)
