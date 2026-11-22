module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.LinearRelationExactSequenceDim
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_relation_exact_sequence_dim : ∀ (k : Type) [Field k] (H M N Q : Type) [AddCommGroup H] [Module k H] [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N] [AddCommGroup Q] [Module k Q] [Module.Finite k M] [Module.Finite k N] (a : H →ₗ[k] M) (b : M →ₗ[k] N) (R : Submodule k (N × Q)), Function.Injective a → LinearMap.range a = LinearMap.ker b → (∀ n, ∃ q, (n, q) ∈ R) → (∀ q, ∃ n, (n, q) ∈ R) → (∀ q, (0, q) ∈ R → q = 0) → (∀ n, (n, 0) ∈ R ↔ n ∈ LinearMap.range b) → Module.Finite k Q ∧ finrank k Q + finrank k M = finrank k H + finrank k N := by
  first | exact @GlobalTheory.CompanionTheory.InertiaEigenvalues.finrank_along_relation | exact GlobalTheory.CompanionTheory.InertiaEigenvalues.finrank_along_relation | (intros; apply GlobalTheory.CompanionTheory.InertiaEigenvalues.finrank_along_relation <;> assumption)
