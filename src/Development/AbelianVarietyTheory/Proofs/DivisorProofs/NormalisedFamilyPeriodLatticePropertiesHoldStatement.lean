module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyPeriodLatticePropertiesHold
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_periodLattice_properties_hold : GlobalTheory.ColNorms.PeriodLattices := by
  first | exact @GlobalTheory.ColNorms.periodLattices | exact GlobalTheory.ColNorms.periodLattices | (intros; apply GlobalTheory.ColNorms.periodLattices <;> assumption)
