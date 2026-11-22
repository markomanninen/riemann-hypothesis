module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairCountBoundOfSiegelMassRatios
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.termPairCountBound_of_siegelMassRatios : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.TypeAsm.PairsP := by
  first | exact @GlobalTheory.TypeAsm.pair_count_bound_of_siegel_mass | exact GlobalTheory.TypeAsm.pair_count_bound_of_siegel_mass | (intros; apply GlobalTheory.TypeAsm.pair_count_bound_of_siegel_mass <;> assumption)
