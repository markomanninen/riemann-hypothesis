module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationTwoAndConjugationAtQAndDStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionOverQOrDEqUnramifiedSupSqrtStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtNegPrimeMemPadicCyclotomicStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtNegPrimeNotMemMaxUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StructureUnramifiedAdjoinSqrtNegPrimeStatement

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.LocalFieldsQD

theorem main : ∀ D : D7, EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D := by
  intro D
  refine ⟨fun i hi w hw => ?_, GlobalTheory.T.aux_statement D⟩
  obtain ⟨M, hM, y, hy, hK⟩ := GlobalTheory.T.completion_over_q_or_d_eq_unramified_sup_sqrt D i hi w hw
  obtain ⟨-, -, hq8, hd16, -⟩ := D.host.hyp
  have h4 : D.nd.l i % 4 = 3 := by rcases hi with h | h <;> rw [h] <;> omega
  have h2 : D.nd.l i ≠ 2 := by omega
  obtain ⟨e1, e2, e3, e4⟩ := GlobalTheory.T.structure_unramified_adjoin_sqrt_neg_prime (D.nd.l i) h2 (D.nbr i w hw).Kw M y hM hy
    (GlobalTheory.T.sqrt_neg_prime_not_mem_max_unramified _ y hy) (GlobalTheory.T.sqrt_neg_prime_mem_padic_cyclotomic _ h4 y hy) hK
  exact ⟨⟨y, hy, e1⟩, e2, e3, e4⟩

end GlobalTheory.LocalFieldsQD
