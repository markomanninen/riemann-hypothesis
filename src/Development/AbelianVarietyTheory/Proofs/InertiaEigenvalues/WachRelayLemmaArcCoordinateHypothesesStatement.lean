module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachRelayLemmaArcCoordinateHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachRelayLemma_arcCoordinateHypotheses : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.RelayArcLifting D HW F ∧ UnusedSlot80.AdmArcA D HW F Cm := by
  first | exact @GlobalTheory.NQ.relay_and_arc_inputs | exact GlobalTheory.NQ.relay_and_arc_inputs | (intros; apply GlobalTheory.NQ.relay_and_arc_inputs <;> assumption)
