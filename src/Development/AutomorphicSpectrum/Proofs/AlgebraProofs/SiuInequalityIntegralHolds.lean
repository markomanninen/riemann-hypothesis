module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.OfRemaining
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanGenericPointSectionInput
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanInputNefAmpleSectionCount
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KodairaGenericOfAmpleSectionCount

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem siuZ : SiuZStatement := by
  have hR4 := GlobalTheory.CompanionTheory.Relay.kleiman_genericPointSectionInput
  obtain ⟨-, hVA, hSC⟩ := GlobalTheory.CompanionTheory.Relay.kleiman_input_nef_ample_section_count hR4
  exact GroundTheory.Heights₂.Heights.ForSecondHalf.SiuZB.of_kodaira (GlobalTheory.CompanionTheory.Relay.kodaira_generic_of_ample_section_count hVA hSC)

end GlobalTheory.CompanionTheory.Ar.Giv
