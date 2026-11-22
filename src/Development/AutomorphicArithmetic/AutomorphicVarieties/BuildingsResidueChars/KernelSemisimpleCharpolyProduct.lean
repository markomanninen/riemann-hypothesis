module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero

@[expose] public section

open Formalism.MainNotions.N


private theorem ker_transfer {Γ K : Type} [Group Γ] [Field K] {n m : ℕ} (ρ : Γ →* GL (Fin n) K)
    (σ : Γ →* GL (Fin m) K) (hρ : IsSSRep ρ) (hσ : IsSSRep σ)
    (hc : ∀ g, ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) K).charpoly =
      ((σ g : GL _ _) : Matrix (Fin m) (Fin m) K).charpoly) (s : Γ) (h : ρ s = 1) : σ s = 1 := by
  have hnm : n = m := by
    have h1 := congrArg Polynomial.natDegree (hc 1)
    rwa [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Fintype.card_fin] at h1
  subst hnm
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ σ hρ hσ hc
  have h1 := hP s
  rw [h] at h1
  simpa using h1
