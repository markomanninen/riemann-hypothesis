module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRep
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple

@[expose] public section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep : ∀ (k Γ : Type) [Field k] [CharZero k] [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) k), IsSSRep r → ∀ M ∈ Submodule.span k (Set.range fun g => ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)), (∀ g, (M * ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k)).trace = 0) → M = 0 := by
  first | exact @GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero | exact GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero | (intros; apply GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero <;> assumption)
