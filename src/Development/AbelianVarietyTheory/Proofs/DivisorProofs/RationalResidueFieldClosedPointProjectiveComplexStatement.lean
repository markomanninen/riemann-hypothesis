module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalResidueFieldClosedPointProjectiveComplex
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProjOverLocallyOfFiniteType

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalResidueField_closedPoint_projectiveComplex : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ x : X,
    IsClosed ({x} : Set X) → RatRes (Cartier.constFn p) (locRing x) := by
  first | exact @GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver | exact GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver | (intros; apply GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver <;> assumption)
