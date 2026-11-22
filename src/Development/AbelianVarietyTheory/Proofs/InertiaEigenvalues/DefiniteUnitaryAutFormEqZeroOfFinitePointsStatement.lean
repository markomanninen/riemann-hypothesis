module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePoints
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryAutForm_eq_zero_of_finitePoints : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (φ : UA L n → ℂ), IsAutFormU φ → (∀ y ∈ finU (E := L) (n := n), φ y = 0) → φ = 0 := by
  first | exact @GlobalTheory.DefiniteDense.eq_zero_of_finU | exact GlobalTheory.DefiniteDense.eq_zero_of_finU | (intros; apply GlobalTheory.DefiniteDense.eq_zero_of_finU <;> assumption)
