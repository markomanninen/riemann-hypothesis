module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddGroupFGLineBundleSectionsArithmeticVariety
public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addGroupFG_lineBundleSections_arithmeticVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ B : LB X, B.IsLB → AddGroup.FG B.Sec := by
  first | exact @GlobalTheory.addGroupFG_sec_of_isArithVar | exact GlobalTheory.addGroupFG_sec_of_isArithVar | (intros; apply GlobalTheory.addGroupFG_sec_of_isArithVar <;> assumption)
