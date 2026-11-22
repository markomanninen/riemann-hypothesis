module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionParabolicEquivariant

@[expose] public section

open PositivityTheory.RgBcC (GLs)
open PositivityTheory.RgBcC.RealD (IsLev)
open GlobalTheory.CompanionTheory.ModelS (Pb fRaw)

theorem _root_.GlobalTheory.T.inducedFunction_parabolic_equivariant :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ lev : Fin n → ℕ, IsLev lam lev →
      ∀ p ∈ Pb lev, ∀ g ∈ GLs n, fRaw lam lev (p * g) = fRaw lam lev p * fRaw lam lev g :=
  GlobalTheory.CompanionTheory.ModelS.FMul.fRaw_mul
