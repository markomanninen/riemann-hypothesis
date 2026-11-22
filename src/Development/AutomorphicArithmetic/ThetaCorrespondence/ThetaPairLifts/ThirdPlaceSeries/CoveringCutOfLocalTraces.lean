module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorIdempotentOfGroupAlgebraIdemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedProjectorOrthogonalOfUnitaryActionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSmulTwistedProjectorMemIntegralFormsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupIdempotentCoefficients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ActsUnitarilyOfClauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGroupOrderBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CutAtOfRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop
namespace GlobalTheory.CovTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem covering_cut_of_local_traces_alt (_h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : _root_.GlobalTheory.CovTop.LiftTruncation := by
  refine (_root_.GlobalTheory.CovTop.Sizes.hostN_alt 3).imp fun Fm CH _ h => ?_
  obtain ⟨C, -, x0, hx⟩ := h
  exact ⟨0, le_rfl, x0, fun x hx' hle ι p hp i => _root_.GlobalTheory.CovTop.cutAt_of_rows_alt p hp.1 hp.2 i _ _ (hx x hx' hle ι p hp i)⟩
end GlobalTheory.CovTop
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftTruncation_of_prints : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.LiftTruncation := by
  first | exact @_root_.GlobalTheory.CovTop.covering_cut_of_local_traces_alt | exact _root_.GlobalTheory.CovTop.covering_cut_of_local_traces_alt | (intros; apply _root_.GlobalTheory.CovTop.covering_cut_of_local_traces_alt <;> assumption)
end
end
