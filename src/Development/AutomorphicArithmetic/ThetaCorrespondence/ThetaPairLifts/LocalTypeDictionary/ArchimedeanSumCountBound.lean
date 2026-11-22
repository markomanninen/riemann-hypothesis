module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfCountAtOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DatumCountBoundLargeDataStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosineCountOfHyp
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorCountBoundOfCosetDepthBound
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKCosetCountFormula

@[expose] public section

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
namespace GlobalTheory.SumCount
theorem archimedean_sum_count_bound : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DepthK → InfCountK := fun hP hD =>
  infCountK_of GlobalTheory.T.datumCountBound_largeData (_root_.GlobalTheory.T.theta_kCoset_count_formula hP) (GlobalTheory.T.pureTensorCountBound_of_cosetDepthBound hD)
end GlobalTheory.SumCount
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_count_bound_archimedean : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DepthK → InfCountK := by
  first | exact @_root_.GlobalTheory.SumCount.archimedean_sum_count_bound | exact _root_.GlobalTheory.SumCount.archimedean_sum_count_bound | (intros; apply _root_.GlobalTheory.SumCount.archimedean_sum_count_bound <;> assumption)
end
