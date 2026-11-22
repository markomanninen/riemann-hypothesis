module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsWeierstrassPSeries
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_isWeierstrassPSeries : ∀ (K : Type) [Field K] [CharZero K] (a b : K), ∃! P : PowerSeries K, IsWpSer a b P := by
  first | exact @GlobalTheory.WpSeries.existsUnique_isWpSer | exact GlobalTheory.WpSeries.existsUnique_isWpSer | (intros; apply GlobalTheory.WpSeries.existsUnique_isWpSer <;> assumption)
