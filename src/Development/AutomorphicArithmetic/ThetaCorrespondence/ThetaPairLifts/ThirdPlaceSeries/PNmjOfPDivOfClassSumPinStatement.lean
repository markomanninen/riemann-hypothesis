module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RowSideOfCompatibleThetaPair
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Formalism.LocalRingCardinality.DataNChTie
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.IndefiniteReal.RealPins
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionFirst
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionSecond
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeFamilyAdoptionThird
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PtOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PNmjOfPDivOfClassSumPin

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pNmj_of_pDiv_classSumPin : ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.Ind.PointSummands D O c), _root_.GlobalTheory.Fc.Ind.DivisorPointSummands D O c b → GlobalTheory.ExportPin.ClassSumPin b.pt → _root_.GlobalTheory.Fc.Ind.NormJumpPointSummands D O c b := by
  first | exact @_root_.GlobalTheory.Fc.Ind.pNmj_of_pDiv_of_classSumPin_alt | exact _root_.GlobalTheory.Fc.Ind.pNmj_of_pDiv_of_classSumPin_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.pNmj_of_pDiv_of_classSumPin_alt <;> assumption)
end
