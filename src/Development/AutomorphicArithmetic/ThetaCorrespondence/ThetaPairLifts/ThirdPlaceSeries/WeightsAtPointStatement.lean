module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.VolMeasureOfAdd
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPoint

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_parameter_strict_antitone_alt : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i PP _ => (i : ℕ) + 1 < (Fm.D x ι).R.m → 1 ≤ (dat p i).p ∧ 1 ≤ (dat p i).q ∧ 2 < Module.finrank ℚ (Fm.D x ι).host.E / 2 ∧ (∀ u1, Quo p i PP u1 → u1 = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁) ∧ (∀ τ, StrictAnti ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ) ∧ StrictAnti (CompHt.uPrime (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ)) ∧ (∃ w : Psi p.T.Q.H → ℤ, (∀ τ, |w τ| ≤ 3 * ((Fm.D x ι).R.r : ℤ)) ∧ uM p i = (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP) + GlobalTheory.FlatLine.parWt (dat p i) w) ∧ ∀ s : ℕ, s ≤ 3 → ∀ τ, Antitone (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ) ∧ Antitone (((lenT p i PP + CompHt.dimFlag (dat p i) + (if s = 0 then 3 else 4) : ℕ) : ℤ) • (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ τ - (uM p i τ + (s * cZero (Fm.D x ι) ((i : ℕ) + 1)) • hodgeWt (dat p i) τ)) := by
  first | exact @_root_.GlobalTheory.QuoWt.weights_at_point_alt | exact _root_.GlobalTheory.QuoWt.weights_at_point_alt | (intros; apply _root_.GlobalTheory.QuoWt.weights_at_point_alt <;> assumption)
end
