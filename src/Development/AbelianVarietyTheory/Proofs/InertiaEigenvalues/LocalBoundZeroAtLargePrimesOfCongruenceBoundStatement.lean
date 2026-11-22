module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundZeroAtLargePrimesOfCongruenceBound
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBoundZeroAtLargePrimes_of_congruenceBound : ∀ (D : D7) (L : SizeData₂ D) (r : FamilyRepresentationConstants.RFam D) (ρ : FamilyRepresentationConstants.RhoFam D) (exc : Finset ℕ), GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.CongBound_at D L → GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D → GlobalTheory.PtCore.PtFam D r ρ → KillingConditions.KillAt ρ → TwistedPlaces.ShaFinOdd D → 3 ≤ TwistedPlaces.lStar L → (exc : Set ℕ) = GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.Exc L → StarE L ρ exc := by
  first | exact @GlobalTheory.NLink.RowE.main | exact GlobalTheory.NLink.RowE.main | (intros; apply GlobalTheory.NLink.RowE.main <;> assumption)
