module

public import Mathlib
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelSqYBoundAtRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leafLevelSq_and_leafYBound : _root_.GlobalTheory.BigOn.ForallRecordObjects fun Fm x _ i p _ O => LeafLevelSq O (Res (R2 p)) (Fm.D x i).R.f ∧ LeafYBound O := by
  first | exact @_root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt | exact _root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt | (intros; apply _root_.GlobalTheory.BigOn.levelSq_yBound_atRec_alt <;> assumption)
end
