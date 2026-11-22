module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdan
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobalDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GaloisRepOfPolarizedPair
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.CaraianiLocalGlobal

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_of_gelfand_kazhdan : GlobalTheory.Published.GelfandKazhdanDual → (GlobalTheory.Published.CaraianiLocalGlobalDual → GlobalTheory.Published.CaraianiLocalGlobal) ∧ (GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) := by
  first | exact @GlobalTheory.galoisRepOfPolarizedCuspidal_iff_pair | exact GlobalTheory.galoisRepOfPolarizedCuspidal_iff_pair | (intros; apply GlobalTheory.galoisRepOfPolarizedCuspidal_iff_pair <;> assumption)
