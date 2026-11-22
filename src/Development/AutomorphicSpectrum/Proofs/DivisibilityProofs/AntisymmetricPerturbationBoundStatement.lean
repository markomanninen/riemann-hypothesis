module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.AntisymmetricPerturbationBound
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antisymmetric_perturbation_bound :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (R : RP Ψ N →ₗ[ℝ] ℝ)
      (v ε : ℝ) (Pl l : MvPolynomial (Ψ × Fin N) ℝ),
      0 < v →
      (∀ lam : Wt Ψ N, eval (fun x => lam x.1 x.2) Pl = R (linRoot lam ^ (dimFl Ψ N + 1))) →
      Pl.IsHomogeneous (dimFl Ψ N + 1) →
      l ∈ GroundTheory.Heights₂.Heights.antisymInv Ψ N j →
      (∀ m, |AddMonoidAlgebra.coeff (Pl - GroundTheory.Heights₂.Heights.antisymDelta Ψ N * l) m| ≤ ε) →
      ∃ α β : Ψ → ℝ, ∀ m : Ψ × Fin N →₀ ℕ, m.degree = dimFl Ψ N + 1 →
        |R (monomial m 1) + v * (∑ τ, (α τ - β τ) * Sh j τ (monomial m 1) +
          ∑ τ, β τ * Tot τ (monomial m 1))| ≤ ε :=
  @GlobalTheory.CompanionTheory.Ar.Top.cor_b_poly_functional
