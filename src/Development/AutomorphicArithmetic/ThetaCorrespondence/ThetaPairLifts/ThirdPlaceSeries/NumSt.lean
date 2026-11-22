module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SumExpSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtPtsImp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterLargeAllPointsBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterHeightLtGenus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaPrimeAllPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoEntryValuesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoBlockConstantCentredStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoWindowContainsCloudStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoLowsDistanceBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoThickPlaceCentreWindowStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoNonThickPlaceCentreWidthStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoEntriesLeFloorHeightStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ModelStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParOfHypStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsBigStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParOfFurtherStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsHLtGStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtPtsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtsOkStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
namespace GlobalTheory.ExpTie
theorem numSt_alt : _root_.GlobalTheory.ExpTie.NumStAlt := by
  have H := _root_.GlobalTheory.ExpTie.atPts_and_alt (_root_.GlobalTheory.ExpTie.atPts_and_alt (_root_.GlobalTheory.ExpTie.atPts_and_alt _root_.GlobalTheory.T.parOf_hyp_at_pts _root_.GlobalTheory.T.exists_large_parameter_estimates_at_pts) (_root_.GlobalTheory.ExpTie.atPts_and_alt _root_.GlobalTheory.T.parameter_large_at_all_points _root_.GlobalTheory.T.parOf_height_lt_genus_at_pts))
    (_root_.GlobalTheory.ExpTie.atPts_and_alt _root_.GlobalTheory.T.isLamPrime_at_all_points _root_.GlobalTheory.T.weight_lambda_shift_nonneg')
  refine _root_.GlobalTheory.ExpTie.atPts_mono H fun Fm x hx i p h j => ?_
  obtain ⟨⟨⟨hH, hR⟩, ⟨hL, hB⟩⟩, ⟨hF, hW⟩⟩ := h
  obtain ⟨W, hOk, hlam, hbox, hT, hSp⟩ := hW j
  refine ⟨parOf (Fm.L x i) j, W, ?_, hH j, hL j, hOk, hR j⟩
  exact
    { k := rfl, m := rfl, t := rfl, f := rfl
      card := Nat.card_eq_fintype_card.trans (Fm.D x i).what₂.card_Tau
      Nr := rfl, x := rfl, log := rfl, b := rfl
      lam := hlam, forced := hF j, box := hbox, thick := hT, special := hSp, big := hB j }
end GlobalTheory.ExpTie
end
end
