module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_rational_conj_mem_boundedCompact : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J : Subgroup (GAf L n)), IsBounded J → ∀ t : GAf L n, Finite {γ : GQ L n // t⁻¹ * (γ : GAf L n) * t ∈ J} := by
  first | exact @GlobalTheory.StabFin.finite_conj_mem | exact GlobalTheory.StabFin.finite_conj_mem | (intros; apply GlobalTheory.StabFin.finite_conj_mem <;> assumption)
