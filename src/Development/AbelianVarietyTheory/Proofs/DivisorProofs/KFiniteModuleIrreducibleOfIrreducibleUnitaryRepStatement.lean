module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteModuleIrreducibleOfIrreducibleUnitaryRep

@[expose] public section

open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset)
open CompanionTheory.D.LK (IsKMod)

theorem GlobalTheory.T.kFiniteModule_irreducible_of_irreducible_unitaryRep :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H)
      (E : Fin n → Fin n → Module.End ℂ D),
      CompleteSpace H → IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → IsKMod ε σ D E →
      ∀ N : Submodule ℂ D, (∀ a b, ∀ x ∈ N, E a b x ∈ N) → N = ⊥ ∨ N = ⊤ :=
  @GlobalTheory.KFinIrr.kMod_irred
