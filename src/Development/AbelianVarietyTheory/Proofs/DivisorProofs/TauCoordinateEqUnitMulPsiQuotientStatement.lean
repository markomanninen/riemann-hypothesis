module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauCoordinateEqUnitMulPsiQuotient
public import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiCoordinateEqUnitMulTauCoordinate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tauCoordinate_eq_unit_mul_psi_quotient : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (a b : D.X)
    (x x₁ x₂ x₃ : (FractionRing R)ˣ), IsTauCoord D a b x → IsPsiCoord D (a + b) x₁ → IsPsiCoord D a x₂ →
      IsPsiCoord D b x₃ → ∃ u : Rˣ, (x : FractionRing R) =
        algebraMap R (FractionRing R) u * x₁ * (x₂ : FractionRing R)⁻¹ * (x₃ : FractionRing R)⁻¹ := by
  first | exact @GlobalTheory.TauCoordQuot.main | exact GlobalTheory.TauCoordQuot.main | (intros; apply GlobalTheory.TauCoordQuot.main <;> assumption)
