module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDegreePullbackEqReducedIntersectionNumbe
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSemipositiveFibrewise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveModelRationalDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DimensionOfDominantFlatCover
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
open Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalDegree_pullback_eq_reducedIntersectionNumber : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (Z : Closeds (ratFibre p)), IsCompleteCurve ℚ Z → ∀ (W : Scheme.{0}) (w : W ⟶ X) (z : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ W), IsArithVar (w ≫ p) 1 → z ≫ w = redι Z ≫ ratFibre.fst p → IsPullback z (redι Z ≫ ratFibre.snd p) ((w ≫ p) ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ)) → ∀ M : LB X, M.IsLB → ratDeg (w ≫ p) (M.pull w) = interNumRed ℚ Z ![M.pull (ratFibre.fst p)] := by
  first | exact @GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed | exact GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed | (intros; apply GlobalTheory.RatFibreClosure.ratDeg_pull_eq_interNumRed <;> assumption)
