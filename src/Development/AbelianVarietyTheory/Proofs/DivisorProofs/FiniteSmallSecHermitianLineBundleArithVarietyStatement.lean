module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSmallSecHermitianLineBundleArithVariety
public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_smallSec_hermitian_line_bundle_arith_variety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ M : HermLB p, M.smallSec.Finite := by
  first | exact @GlobalTheory.SmallFin.smallSec_finite | exact GlobalTheory.SmallFin.smallSec_finite | (intros; apply GlobalTheory.SmallFin.smallSec_finite <;> assumption)
