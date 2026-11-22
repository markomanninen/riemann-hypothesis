module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanGenericPointSectionInput
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kleiman_genericPointSectionInput : GroundTheory.Heights₂.Heights.Kleiman.GenericPointSectionInput.Statement.{0, 0} := by
  first | exact @GlobalTheory.CompanionTheory.Relay.kleiman_genericPointSectionInput | exact GlobalTheory.CompanionTheory.Relay.kleiman_genericPointSectionInput | (intros; apply GlobalTheory.CompanionTheory.Relay.kleiman_genericPointSectionInput <;> assumption)
