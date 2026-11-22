module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldsAtAuxiliaryPrimes
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
theorem _root_.GlobalTheory.T.local_fields_at_auxiliary_primes : ∀ D : D7, EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D := by
  first | exact @GlobalTheory.LocalFieldsQD.main | exact GlobalTheory.LocalFieldsQD.main | (intros; apply GlobalTheory.LocalFieldsQD.main <;> assumption)
