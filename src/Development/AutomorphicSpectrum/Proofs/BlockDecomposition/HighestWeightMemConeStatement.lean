module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightMemCone

@[expose] public section

open PositivityTheory.RgBcC.RealD (inCone)

theorem GlobalTheory.T.highest_weight_mem_cone :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (K : Fin n → Fin n → Module.End ℂ V),
      Formalism.REAL.GlRel K → ∀ lev : Fin n → ℕ, Monotone lev →
      ∀ (ev : V →ₗ[ℂ] ℂ) (μ ν : Fin n → ℝ) (x : V),
        Formalism.REAL.KHighest (fun _ => true) K ν x →
        (∀ a b v, lev a = lev b → a ≠ b → ev (K a b v) = 0) →
        (∀ a v, ev (K a a v) = (μ a : ℂ) * ev v) →
        (∃ T ∈ Algebra.adjoin ℂ {T : Module.End ℂ V | ∃ a b, T = K a b}, ev (T x) ≠ 0) →
        inCone lev (ν - μ) :=
  GlobalTheory.CompanionTheory.HighestCone.inCone_of_highest
