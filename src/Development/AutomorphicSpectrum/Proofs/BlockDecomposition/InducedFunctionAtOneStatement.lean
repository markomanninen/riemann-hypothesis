module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedFunctionAtOne

@[expose] public section

theorem GlobalTheory.T.inducedFunction_at_one :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (lev : Fin n → ℕ),
      GlobalTheory.CompanionTheory.ModelS.fRaw lam lev 1 = 1 :=
  GlobalTheory.CompanionTheory.ModelS.fRaw_one
