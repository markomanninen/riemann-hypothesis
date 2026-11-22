module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusOneDatumModelLatticeAlgebraicData
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genus_one_datum_model_lattice_algebraic_data : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → IsWq g.W g.wq ∧ IsLat g.abelian₂ ∧ g2 g.abelian₂ ∈ Qbar ∧ g3 g.abelian₂ ∈ Qbar ∧ AlgEnt (sgStar g.abelian₂) ∧ ∃ v : ℂ, v ∉ g.abelian₂ ∧ wpF g.abelian₂ v ∈ Qbar := by
  first | exact @GlobalTheory.FrobStick.AtData.atData | exact GlobalTheory.FrobStick.AtData.atData | (intros; apply GlobalTheory.FrobStick.AtData.atData <;> assumption)
