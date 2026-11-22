module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicGroupAlgebraActionInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqPowOfModEqSim

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicGroupAlgebraAction_injective : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : GlobalTheory.LKGeo.Link D G), Function.Injective (GlobalTheory.LKGeo.actOn L.rep (AfP p)) := by
  exact GlobalTheory.LKGeo.actOn_rep_afP_injective
