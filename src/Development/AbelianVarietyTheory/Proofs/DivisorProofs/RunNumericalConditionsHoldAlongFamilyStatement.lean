module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamily
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TiedRecordExistsOfActionPin
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeafDataOfOnTieOfIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LiftWeightComplexPointEqTwist
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeavesSupSpanLemmaSOfFormTieK
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthPageFirstZetaFactorEqPrimePower
public import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepthAllRun
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ColengthBoundSplitPlaceChart
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateInclusionChartCharacters
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UnramifiedCompanionChartCharacters
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional

@[expose] public section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.runNumericalConditions_hold_along_family : ∀ x₁ : ℝ, Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, PageNum (Fm.parT x hx ι) x₁ ∧ 3 ≤ (Fm.L x ι).sc.x ∧ ((Fm.D x ι).R.k : ℝ) * (Fm.L x ι).sc.b' ≤ (Fm.L x ι).sc.b ∧ 3 ≤ (Fm.L x ι).sc.x ^ ((Fm.L x ι).sc.ez / 5) ∧ 8 * (Fm.D x ι).R.f * (Fm.D x ι).R.r + 4 ≤ (Fm.D x ι).R.nV := by
  first | exact @GlobalTheory.OntoNum.pageNum_along | exact GlobalTheory.OntoNum.pageNum_along | (intros; apply GlobalTheory.OntoNum.pageNum_along <;> assumption)
