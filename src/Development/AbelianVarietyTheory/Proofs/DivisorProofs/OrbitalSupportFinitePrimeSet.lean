module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntCZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHodgeLatticeGermSystem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistedUnitCommutes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugatePairsSameSimilitude
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSupportTwistedHeckeTestFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormUnitCommutation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalConjTrivializationAtPlaceAwayPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistedNormConclusionTransferRingEquivStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CofinitePlacesRealizePrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjugationStableStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutantOfMaximalDegreeElement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCentralizerInjectiveCommutantEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqSubmoduleMulLeftImageIntegralClosureOfSeparabl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedOfIsIntegral
public import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingUnitsIntegralCofinite

@[expose] public section

noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

namespace GlobalTheory.FinClsLoc

theorem starT_invol {p : ℕ} [Fact p.Prime] (G : HTGroup p) (K : Type) [CommRing K] [Algebra ℚ K]
    (x : K ⊗[ℚ] G.C) : (starT G.star K (starT G.star K x).unop).unop = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c => rw [starT_tmul, starT_tmul, G.star_star]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

end GlobalTheory.FinClsLoc
