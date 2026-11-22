module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankAdjoinVarsField

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_adjoin_vars_field :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (I : Type) (d : ℕ),
      0 < d →
      (letI : Algebra Ω₀ Ω := fn.toAlgebra
       Module.finrank Ω₀ Ω = d) →
      letI : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
        ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra
      Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
        algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)))
        (FractionRing (MvPolynomial I Ω)) = d := by
  intro Ω₀ Ω _ _ fn I d hd hfin
  let : Algebra Ω₀ Ω := fn.toAlgebra
  have : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)
  let : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
    ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra
  have hdegree :=
    GlobalTheory.CompanionTheory.FieldDeg.finrank_fraction_over_adjoin_X_eq Ω₀ Ω I rfl
  exact hdegree.trans hfin
