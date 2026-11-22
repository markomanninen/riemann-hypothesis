module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowSideCardEqOfCoord
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PRowsOfParts

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bundle_lines_of_primitive_frames_div_nmj : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.FiringPointSummands D O c b → _root_.GlobalTheory.Fc.Ind.summandRealBound D O c b → _root_.GlobalTheory.Fc.Ind.summandPrimitive D O c b → _root_.GlobalTheory.Fc.Ind.FramePointSummands D O c b → _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b → _root_.GlobalTheory.Fc.Ind.NormJumpPointSummands D O c b → Formalism.BasicNotions.GoodFTAll D → b.pt.CompatibilityConditions → _root_.GlobalTheory.Fc.Ind.RowPointSummands D O c b := by
  first | exact @_root_.GlobalTheory.Fc.Ind.pRows_of_parts_alt | exact _root_.GlobalTheory.Fc.Ind.pRows_of_parts_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.pRows_of_parts_alt <;> assumption)
end
