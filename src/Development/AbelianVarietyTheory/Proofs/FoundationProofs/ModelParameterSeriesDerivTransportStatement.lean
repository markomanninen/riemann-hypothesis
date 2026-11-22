module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModelParameterSeriesDerivTransport
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformises

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_parameter_series_deriv_transport : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F) := by
  first | exact @GlobalTheory.DerivTransport.atU_deriv | exact GlobalTheory.DerivTransport.atU_deriv | (intros; apply GlobalTheory.DerivTransport.atU_deriv <;> assumption)
