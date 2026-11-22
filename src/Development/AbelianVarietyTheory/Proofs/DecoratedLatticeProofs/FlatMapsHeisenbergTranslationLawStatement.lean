module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsHeisenbergTranslationLaw
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMaps_heisenbergTranslation_law : ∀ D : D7, GlobalTheory.FinPl.FlatShift D := by
  first | exact @GlobalTheory.FlatShiftPf.flatShift | exact GlobalTheory.FlatShiftPf.flatShift | (intros; apply GlobalTheory.FlatShiftPf.flatShift <;> assumption)
