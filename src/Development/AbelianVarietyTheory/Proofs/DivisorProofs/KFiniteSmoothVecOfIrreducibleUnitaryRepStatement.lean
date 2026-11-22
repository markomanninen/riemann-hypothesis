module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSmoothVecOfIrreducibleUnitaryRep

@[expose] public section

open Formalism.REAL (inG)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin)

theorem _root_.GlobalTheory.T.kFinite_smoothVec_of_irreducible_unitaryRep :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
      IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ v, IsKFin ε σ v →
        Formalism.L2.Theta.SmoothVec {X | inG ε X} σ v :=
  GlobalTheory.HdSmooth.kFinite_smoothVec
