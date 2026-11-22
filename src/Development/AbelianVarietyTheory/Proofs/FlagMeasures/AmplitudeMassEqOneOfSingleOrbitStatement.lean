module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeMassEqOneOfSingleOrbit
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTermsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolumeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFactsStatement

@[expose] public section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitude_mass_eq_one_of_single_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (P : Submodule L.O S.V → Prop), (∃ Λ, S.IsTerm d Λ) → (∀ Λ Λ', S.IsTerm d Λ → S.IsTerm d Λ' → ∃ h ∈ S.St, Λ' = h • Λ) → (∀ Λ, S.IsTerm d Λ → P Λ ∧ S.mu Λ = 1 ∧ S.om d Λ = 1) → S.amp d P = 1 ∧ S.mass d P = 1 := by
  first | exact @GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit | exact GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit | (intros; apply GlobalTheory.HL.Frames.amp_mass_eq_one_of_one_orbit <;> assumption)
