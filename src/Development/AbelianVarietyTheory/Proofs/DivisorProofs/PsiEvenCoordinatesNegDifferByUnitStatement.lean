module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEvenCoordinatesNegDifferByUnit
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
theorem _root_.GlobalTheory.T.psiEven_coordinates_neg_differ_by_unit : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.PsiEven →
    ∀ (y : D.X) (x x' : (FractionRing R)ˣ), IsPsiCoord D y x → IsPsiCoord D (-y) x' →
      ∃ u : Rˣ, (x' : FractionRing R) = algebraMap R (FractionRing R) u * x := by
  first | exact @GlobalTheory.PsiEvenCoordUnit.main | exact GlobalTheory.PsiEvenCoordUnit.main | (intros; apply GlobalTheory.PsiEvenCoordUnit.main <;> assumption)
