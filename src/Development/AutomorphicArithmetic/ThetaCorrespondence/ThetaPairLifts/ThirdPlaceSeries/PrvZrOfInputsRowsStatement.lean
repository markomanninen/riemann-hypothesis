module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputs
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PrvZrOfInputsRows
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reducedMultiplicity_of_inputs : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → _root_.GlobalTheory.NRows.PointConditions' D → SumRepresentations.ReducedMultiplicityStatement D := by
  first | exact @_root_.GlobalTheory.PtSt.reducedMultiplicity_of_rows' | exact _root_.GlobalTheory.PtSt.reducedMultiplicity_of_rows' | (intros; apply _root_.GlobalTheory.PtSt.reducedMultiplicity_of_rows' <;> assumption)
end
