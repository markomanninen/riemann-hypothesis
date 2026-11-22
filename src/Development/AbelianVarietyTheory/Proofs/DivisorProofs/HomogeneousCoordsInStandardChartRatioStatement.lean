module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousCoordsInStandardChartRatio
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPropeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingElementarySymmetricUnit
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsImmersionProjSpaceOfLocalLinearChange

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousCoords_in_standardChart_ratio : ∀ (o K : Type) [CommRing o] [Field K] (n : ℕ) (x : Sp K ⟶ PSpace o n) (v : Fin (n + 1) → K) (a : Fin (n + 1)), PCrd x v → ⊤ ≤ x ⁻¹ᵁ ProjSpace.chart o n a → v a ≠ 0 ∧ ∀ b, valR x (ProjSpace.chart o n a) (ProjSpace.ratio o n a b) = v b / v a := by
  first | exact @GlobalTheory.UMin.CrdChart.pCrd_chart | exact GlobalTheory.UMin.CrdChart.pCrd_chart | (intros; apply GlobalTheory.UMin.CrdChart.pCrd_chart <;> assumption)
