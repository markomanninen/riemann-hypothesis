module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjOnInterQuadraticKernelsOfTraceEq

@[expose] public section

namespace GlobalTheory.TraceConj

open Formalism.MainNotions.N UpperTheory.V.Af

theorem main : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ)
    (r r' : Γ →* GL (Fin n) k), IsSSRep r → IsSSRep r' →
    (∀ s, ((r s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace =
      ((r' s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → RepIso r r' := by
  intro Γ k _ _ _ n r r' hr hr' htr
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hr hr' (fun g => by
    refine GlobalTheory.QuadKernelConj.charpoly_eq_of_trace_pow _ _ fun m => ?_
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
    exact htr (g ^ m))
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

end GlobalTheory.TraceConj
