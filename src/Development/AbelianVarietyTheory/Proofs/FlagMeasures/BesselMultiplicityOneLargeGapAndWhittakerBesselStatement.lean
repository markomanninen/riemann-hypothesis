module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBessel
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BesselOfWPf

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel : GlobalTheory.GapIn.UniqGap ∧ Formalism.L2.SG.LocWSOf.BesselOfW := by
  first | exact @GlobalTheory.uniqGap_and_besselOfW | exact GlobalTheory.uniqGap_and_besselOfW | (intros; apply GlobalTheory.uniqGap_and_besselOfW <;> assumption)
