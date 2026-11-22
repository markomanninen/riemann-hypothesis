module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndexBoundParameterRequirementsEventuallyFamily
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
theorem _root_.GlobalTheory.T.indexBoundParameterRequirements_eventually_family : Closed FamHyp fun Fm _ => ∃ x0 : ℝ, ∀ (x : ℝ) (hx : Fm.x1 < x), x0 ≤ x → ∀ ι : Fm.Ix x, GlobalTheory.IndexAssembly.SizeRows (Fm.parT x hx ι) (Fm.ex x hx ι).kap_def := by
  first | exact @GlobalTheory.OntoSizeRows.sizeRows_along | exact GlobalTheory.OntoSizeRows.sizeRows_along | (intros; apply GlobalTheory.OntoSizeRows.sizeRows_along <;> assumption)
