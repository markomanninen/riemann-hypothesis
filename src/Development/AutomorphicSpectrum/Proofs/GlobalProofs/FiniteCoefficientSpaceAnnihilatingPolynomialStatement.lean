module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteCoefficientSpaceAnnihilatingPolynomial

@[expose] public section

open GlobalTheory.Published.AutFin (IsContRep coeffSpan)

theorem _root_.GlobalTheory.T.finite_coefficient_space_annihilating_polynomial :
    ∀ (K W : Type) [Group K] [TopologicalSpace K] [AddCommGroup W] [Module ℂ W]
      [FiniteDimensional ℂ W] (ρ : Representation ℂ K W),
      IsContRep ρ → ∀ s : ℝ → K, Continuous s → s 0 = 1 →
        (∀ a b, s (a + b) = s a * s b) →
        ∃ m : Polynomial ℂ, m ≠ 0 ∧ ∀ f ∈ coeffSpan ρ, ∀ k : K,
          ∑ j ∈ Finset.range (m.natDegree + 1),
            m.coeff j * iteratedDeriv j (fun t : ℝ => f (k * s t)) 0 = 0 :=
  GlobalTheory.CompanionTheory.HcFinite.OneParam.coeff_ode
