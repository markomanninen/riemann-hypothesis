module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantCommuteOfCommute

@[expose] public section

open PositivityTheory.RgBcC.RealD (gelA)

theorem _root_.GlobalTheory.T.gelfand_invariant_commute_of_commute :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V) (T : Module.End ℂ V),
      (∀ a b, T * E a b = E a b * T) → ∀ m : ℕ, gelA E m * T = T * gelA E m :=
  GlobalTheory.CompanionTheory.ModelS.gelA_commute_of_units
