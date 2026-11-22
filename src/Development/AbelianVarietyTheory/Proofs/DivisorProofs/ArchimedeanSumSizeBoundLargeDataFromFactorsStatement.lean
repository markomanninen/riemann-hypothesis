module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSumSizeBoundLargeDataFromFactors
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSumSizeBound_largeData_from_factors : SumOKK → DepthK → InfScalK → InfTensK → InfCountK → InfClassK → InfTopK → InfRowK → InfPairK → InfPsiK → InfFormK → InfK := by
  first | exact @GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors | exact GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors | (intros; apply GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors <;> assumption)
