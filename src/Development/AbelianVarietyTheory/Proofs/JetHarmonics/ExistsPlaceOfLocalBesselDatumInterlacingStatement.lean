module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPlaceOfLocalBesselDatumInterlacing
public import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ThresholdProductsBounded
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates

@[expose] public section

open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.QuantumDeterminants GlobalTheory.ThA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_of_localBesselDatum_interlacing : ∀ (k r : ℕ) (L : LocBessel k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (lam0 : Fin (2 * r + k + 1) → ℝ) (hk : k ≤ 2 * r + k + 1), 2 ≤ k → IsSection k r L.z L.z' μsec → InterlaceS hk L.u lam0 → InterlaceS hk L.u' lam0 → ∃ (U U' : ℕ → ℝ) (p : KB.Pl ⟨k, r, Tz k r L.z, Tz k r L.z', U, U'⟩ L.Wp L.Wq), (∀ i : Fin k, U (i.val + 1) = L.u i ∧ U' (i.val + 1) = L.u' i) ∧ IsStdOf L μsec p.T.base := by
  first | exact @GlobalTheory.exists_place_of_locBessel | exact GlobalTheory.exists_place_of_locBessel | (intros; apply GlobalTheory.exists_place_of_locBessel <;> assumption)
