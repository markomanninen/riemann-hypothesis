module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandInvariantEvalLowest

@[expose] public section

open PositivityTheory.RgBcC.RealD (gelA)

theorem GlobalTheory.T.gelfand_invariant_eval_lowest :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (E : Fin n → Fin n → Module.End ℂ V),
      Formalism.REAL.GlRel E → ∀ (ev : V →ₗ[ℂ] ℂ) (x : Fin n → ℂ),
        (∀ a b, b < a → ∀ v, ev (E a b v) = 0) →
        (∀ a v, ev (E a a v) = x a * ev v) →
        ∀ (m : ℕ) (v : V), ev (gelA E m v) =
          GlobalTheory.Dec.gelfVal (fun a => x a + ((n : ℂ) - 1) / 2 - ((a : ℕ) : ℂ)) m * ev v :=
  GlobalTheory.CompanionTheory.EvGel.ev_gelA
