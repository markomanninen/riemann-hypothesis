module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetOfBirational
public import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentialsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveCartierDivisorPullbackOfDominant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.Discrepancy GlobalTheory.EtaleKlt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primeDivisor_over_target_of_birational : ∀ {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp ℂ) (s : Y ⟶ X) [IsDominant s],
    Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E := by
  first | exact @GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective_complex | exact GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective_complex | (intros; apply GlobalTheory.Discrepancy.DivOver.exists_over_of_bijective_complex <;> assumption)
