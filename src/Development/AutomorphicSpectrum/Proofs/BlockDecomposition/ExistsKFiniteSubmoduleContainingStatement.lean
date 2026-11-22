module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKFiniteSubmoduleContaining

@[expose] public section

open PositivityTheory.RgBcC.RealD (alg kF)

theorem GlobalTheory.T.exists_k_finite_submodule_containing :
    ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (F1 F2 : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel F1 → Formalism.REAL.GlRel F2 →
      (∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) → ∀ f : V,
      (∀ x : V, ∃ T ∈ alg F1 F2, T f = x) → ∀ S₀ : Submodule ℂ V,
      FiniteDimensional ℂ S₀ → f ∈ S₀ → (∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) →
      ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧
        ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S :=
  @GlobalTheory.CompanionTheory.ModelS.LocFin.cyclic_locFin
