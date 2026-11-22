module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistedPrincipalPolarisationSectionsBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditionalStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory


open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.twistBaseChange_and_valuation_statements :
    _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBaseChangeStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBCSpanStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.VRatioGtStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWStatement ∧ _root_.ReciprocityTheory.ChartRestriction.G.DVR.UUStatement := by
  have hbc : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBaseChangeStatement := _root_.GlobalTheory.twistBaseChange
  have hgl : _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt := _root_.GlobalTheory.globalFns_holds
  have hspan : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TwistBCSpanStatement := _root_.ReciprocityTheory.ChartRestriction.G.DVR.twistBCSpan_of hbc
  have hval : _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.VRatioGtStatement := _root_.GlobalTheory.RatioVal.main
  exact ⟨hbc, hspan, hval, _root_.ReciprocityTheory.ChartRestriction.G.DVR.TWM.tw_of hgl hspan hval, _root_.GlobalTheory.UnitBallFree.main hgl hbc⟩

end GlobalTheory
