module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HenselRootsOfLocalFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
public import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterValuesInjectiveLength

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.ConsExists GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_roots_of_distinct_units_roots : ∀ {X O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [HenselianRing O (IsLocalRing.maximalIdeal O)] {t : ℕ} (T : Subalgebra O (X → O)), IsLocalRing T → ∀ (P : X → Polynomial O), (∀ j, (fun x => (P x).coeff j) ∈ T) → (∀ x, (P x).Monic ∧ (P x).natDegree = t) → ∀ (π : X) (d : Fin t → O), (∀ a b, a ≠ b → IsUnit (d a - d b)) → P π = ∏ c, (Polynomial.X - Polynomial.C (d c)) → ∀ x, ∃ β : Fin t → O, Function.Injective β ∧ P x = ∏ c, (Polynomial.X - Polynomial.C (β c)) := by
  first | exact @GlobalTheory.hensel_roots_of_local_family | exact GlobalTheory.hensel_roots_of_local_family | (intros; apply GlobalTheory.hensel_roots_of_local_family <;> assumption)
