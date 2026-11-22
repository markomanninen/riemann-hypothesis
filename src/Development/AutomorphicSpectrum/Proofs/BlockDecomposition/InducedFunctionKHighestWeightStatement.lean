module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionKHighestWeight

@[expose] public section

open PositivityTheory.RgBcC.RealD (IsLev)
open GlobalTheory.CompanionTheory.ModelS (SmF fRaw Kf muZ)

theorem GlobalTheory.T.inducedFunction_k_highest_weight :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam →
      ∀ lev : Fin n → ℕ, IsLev lam lev → ∀ F : SmF n, F.1 = fRaw lam lev →
        (∀ a b : Fin n, a < b → Kf a b F = 0) ∧
          ∀ a : Fin n, Kf a a F = (muZ lam lev a : ℂ) • F :=
  GlobalTheory.CompanionTheory.ModelS.f_highest
