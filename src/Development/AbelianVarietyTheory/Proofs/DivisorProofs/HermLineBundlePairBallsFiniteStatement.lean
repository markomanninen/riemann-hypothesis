module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundlePairBallsFinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.VolGe
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermLineBundlePair_balls_finite : GlobalTheory.Published.ArithHilbertSamuel → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ (a c : ℤ) (R : ℝ), GlobalTheory.Published.ArCalc → (P.Bl a c R).Finite := by
  first | exact @GlobalTheory.VolBr.BallFinite.bl_finite | exact GlobalTheory.VolBr.BallFinite.bl_finite | (intros; apply GlobalTheory.VolBr.BallFinite.bl_finite <;> assumption)
