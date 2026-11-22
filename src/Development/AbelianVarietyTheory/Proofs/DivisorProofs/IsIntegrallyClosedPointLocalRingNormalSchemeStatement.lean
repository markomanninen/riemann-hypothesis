module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedPointLocalRingNormalScheme
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosed_pointLocalRing_normalScheme : ∀ (X : Scheme.{0}) [IsIntegral X] [GlobalTheory.IsNormalScheme X] (x : X),
    IsIntegrallyClosed (locRing x) := by
  first | exact @GlobalTheory.FieldPair.isIntegrallyClosed_locRing | exact GlobalTheory.FieldPair.isIntegrallyClosed_locRing | (intros; apply GlobalTheory.FieldPair.isIntegrallyClosed_locRing <;> assumption)
