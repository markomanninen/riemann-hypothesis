module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivativeCongruenceGermIntegralTranslate
public import Development.AbelianVarietyTheory.Definitions.Jets.ColValMonomial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open GlobalTheory GlobalTheory.FamGerm
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_congruence_germ_integral_translate : Laws → Laws4 → TwistBCSpanStatement → JetSer.JetAlgSt → JetSer.RepSt → JetSer.SerSt → JetSer.SerExSt → JetSer.RosIdSt → JetSer.ChartBCSt → FamGerm.GermExSt → EigGermSt := by
  first | exact @GlobalTheory.EigenGerm.eigen_germ | exact GlobalTheory.EigenGerm.eigen_germ | (intros; apply GlobalTheory.EigenGerm.eigen_germ <;> assumption)
