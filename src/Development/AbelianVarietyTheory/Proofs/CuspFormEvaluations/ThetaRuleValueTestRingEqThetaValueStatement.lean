module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRuleValueTestRingEqThetaValue
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
theorem _root_.GlobalTheory.T.thetaRuleValue_testRing_eq_thetaValue : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : Rul Xo c, IsThRule Xo c nab x P f → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y → ThValAt Xo c nab y x P (evR Xo c f y) := by
  first | exact @GlobalTheory.thValAt_evR_of_fromTest | exact GlobalTheory.thValAt_evR_of_fromTest | (intros; apply GlobalTheory.thValAt_evR_of_fromTest <;> assumption)
