module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNonvanishingDense
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatPrimeDense
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiniteSeparatingModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsNear
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsBounded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPolyNonvanishDense
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNoetherProjection
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRootsLiftToZeros

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem PositivityTheory.Xgn.nonvanishing_points_dense : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (f : MRing ι), IsArithVar P d → f ∉ P → mcPts P ⊆ closure {z | z ∈ mcPts P ∧ evC z f ≠ 0} := by
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.RatPrimeDense.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.FiniteSeparatingModel.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.NoetherProjection.proof
        GroundTheory.Heights₂.Heights.HilbertSamuel.RootsLiftToZeros.proof)
      GroundTheory.Heights₂.Heights.HilbertSamuel.RootsNear.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.RootsBounded.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.PolyNonvanishDense.proof)
