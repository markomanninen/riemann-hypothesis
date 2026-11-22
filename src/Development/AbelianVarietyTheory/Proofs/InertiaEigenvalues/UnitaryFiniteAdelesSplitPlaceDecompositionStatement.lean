module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecomposition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L), (∀ g : GAf L n, ∃ x y : GAf L n, TrivOutside {s.v} x ∧ TrivOutside {s.v}ᶜ y ∧ g = x * y) ∧ (∀ x y : GAf L n, TrivOutside {s.v} x → TrivOutside {s.v}ᶜ y → Commute x y) ∧ (∀ A : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)), ∃! x : GAf L n, TrivOutside {s.v} x ∧ s.loc n x = A) := by
  first | exact @GlobalTheory.SplitAdelic.main | exact GlobalTheory.SplitAdelic.main | (intros; apply GlobalTheory.SplitAdelic.main <;> assumption)
