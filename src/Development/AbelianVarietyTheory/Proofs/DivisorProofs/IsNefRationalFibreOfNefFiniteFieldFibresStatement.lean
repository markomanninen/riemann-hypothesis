module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefRationalFibreOfNefFiniteFieldFibres
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
theorem _root_.GlobalTheory.T.isNef_rationalFibre_of_nef_finiteFieldFibres : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, NefFib L → (letI := GlobalTheory.algebraΓOfHom (Limits.pullback.snd (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))); GlobalTheory.IsNef ℚ (L.B.pull (Limits.pullback.fst (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℚ))))) := by
  first | exact @GlobalTheory.GenNef.isNef_ratFibre | exact GlobalTheory.GenNef.isNef_ratFibre | (intros; apply GlobalTheory.GenNef.isNef_ratFibre <;> assumption)
