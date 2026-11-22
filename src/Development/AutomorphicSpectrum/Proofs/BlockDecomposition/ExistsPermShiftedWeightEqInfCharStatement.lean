module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermShiftedWeightEqInfChar

@[expose] public section

open PositivityTheory.RgBcC (infOf)
open PositivityTheory.RgBcC.RealD (IsLev)

theorem _root_.GlobalTheory.T.exists_perm_shifted_weight_eq_inf_char :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ), IsLev lam lev →
      ∃ σ : Equiv.Perm (Fin n), ∀ a : Fin n,
        (GlobalTheory.CompanionTheory.ModelS.yZ lam lev a : ℂ) + ((n : ℂ) - 1) / 2 -
          ((a : ℕ) : ℂ) = infOf lam false (σ a) :=
  GlobalTheory.CompanionTheory.ModelS.ReversedBlocks.exists_perm_yZ
