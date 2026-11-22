module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsSymplecticBasisPrincipalPolarization
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
public import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplectic_basis_principal_polarization : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ l l' : Λ, ∃ k : ℤ, (hermForm Hm (l : Fin g → ℂ) (l' : Fin g → ℂ)).im = k) →
    (∀ w : Fin g → ℂ, (∀ l : Λ, ∃ k : ℤ, (hermForm Hm w (l : Fin g → ℂ)).im = k) → w ∈ Λ) →
    ∃ bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ, ∀ α β,
      (hermForm Hm (bs α : Fin g → ℂ) (bs β : Fin g → ℂ)).im = Matrix.J (Fin g) ℝ α β := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice.exists_symplectic_basis | exact GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice.exists_symplectic_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.SymplecticLattice.exists_symplectic_basis <;> assumption)
