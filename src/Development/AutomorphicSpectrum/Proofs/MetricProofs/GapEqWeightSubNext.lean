module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPolyTowtBound

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem toWt_toWtS_homogeneous_coeff_bound :
    ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ,
      (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n →
        (toWt Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
          ∀ m, |(toWt Q).coeff m| ≤ Cst * M)) ∧
      ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n →
        (toWtS Q).IsHomogeneous n ∧ ((∀ m, |Q.coeff m| ≤ M) →
          ∀ m, |(toWtS Q).coeff m| ≤ Cst * M) :=
  @PositivityTheory.Xgp.t_poly_towt_bound

end GlobalTheory.CompanionTheory.Ar.PB
