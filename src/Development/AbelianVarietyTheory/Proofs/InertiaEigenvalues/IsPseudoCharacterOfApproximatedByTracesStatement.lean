module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPseudoCharacterOfApproximatedByTraces
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPseudoCharacter_of_approximatedByTraces : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (T : Γ → PadicAlgCl l) (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), PolyApprox T (trc '' C) → IsPsChar a T := by
  first | exact @GlobalTheory.PsChar.isPsChar_of_polyApprox_trc | exact GlobalTheory.PsChar.isPsChar_of_polyApprox_trc | (intros; apply GlobalTheory.PsChar.isPsChar_of_polyApprox_trc <;> assumption)
