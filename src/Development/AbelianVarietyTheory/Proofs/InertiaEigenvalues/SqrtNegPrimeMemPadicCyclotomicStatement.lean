module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtNegPrimeMemPadicCyclotomic
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_neg_prime_mem_padic_cyclotomic : ∀ (l : ℕ) [Fact l.Prime], l % 4 = 3 → ∀ y : Om l, y ^ 2 = -(l : Om l) → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} := by
  first | exact @GlobalTheory.sqrt_neg_l_mem_adjoin_roots_of_unity | exact GlobalTheory.sqrt_neg_l_mem_adjoin_roots_of_unity | (intros; apply GlobalTheory.sqrt_neg_l_mem_adjoin_roots_of_unity <;> assumption)
