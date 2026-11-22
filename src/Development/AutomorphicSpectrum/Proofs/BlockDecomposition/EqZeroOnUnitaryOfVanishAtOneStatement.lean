module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOnUnitaryOfVanishAtOne

@[expose] public section

open GlobalTheory.CompanionTheory.ModelS (SmF Kf)

theorem GlobalTheory.T.eq_zero_on_unitary_of_vanish_at_one :
    ∀ (n : ℕ) (S : Submodule ℂ (SmF n)), FiniteDimensional ℂ S →
      (∀ a b : Fin n, ∀ w ∈ S, Kf a b w ∈ S) → (∀ w ∈ S, w.1 1 = 0) →
      ∀ w ∈ S, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, w.1 k.1 = 0 :=
  GlobalTheory.CompanionTheory.ModelS.Sep.main
