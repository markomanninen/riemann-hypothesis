module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteNetOfGradedProjections
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose

@[expose] public section

open Matrix
open CompanionTheory.RgExh.Dec (IsGrad)
open GlobalTheory.CompanionTheory.PSubFlag (Pm Pp)

theorem _root_.GlobalTheory.T.finite_net_of_graded_projections :
    ∀ (n : ℕ) (ε : Fin n → Bool),
      ∃ (m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ j, IsGrad ε (A j)) ∧
        ∀ A' : Matrix (Fin n) (Fin n) ℂ, IsGrad ε A' →
          ∃ j, Formalism.REAL.hs (Pm (A j) - Pm A') ≤ 1 / 4 ∧
            Formalism.REAL.hs (Pp (A j) - Pp A') ≤ 1 / 4 :=
  GlobalTheory.CompanionTheory.UGeo.GradNet.exists_net
