module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfWeightNumerical
public import Development.AbelianVarietyTheory.Definitions.Divisors.ESmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefTheta
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumPtOfSizes

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_pt_of_wt_pt_num_pt : _root_.GlobalTheory.RefSum.WtPtAlt → _root_.GlobalTheory.RefSum.NumPtAlt → _root_.GlobalTheory.RefSum.SumPtAlt := by
  first | exact @_root_.GlobalTheory.RefSum.sumPt_of_sizes_alt | exact _root_.GlobalTheory.RefSum.sumPt_of_sizes_alt | (intros; apply _root_.GlobalTheory.RefSum.sumPt_of_sizes_alt <;> assumption)
end
