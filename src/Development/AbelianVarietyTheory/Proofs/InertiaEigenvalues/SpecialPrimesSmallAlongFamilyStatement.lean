module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecialPrimesSmallAlongFamily
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
theorem _root_.GlobalTheory.T.specialPrimes_small_along_family : ∀ {eps : ℝ} (Fm : FamP eps), ∀ C : ℝ, 1 ≤ C → ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, Small (Fm.L x i) C ∧ 8 ≤ (Fm.L x i).sc.L ∧ 60 ≤ (Fm.D x i).host.splitBound ∧ C ≤ (Fm.L x i).sc.b := by
  first | exact @GlobalTheory.SpecialSmall.special_primes_small | exact GlobalTheory.SpecialSmall.special_primes_small | (intros; apply GlobalTheory.SpecialSmall.special_primes_small <;> assumption)
