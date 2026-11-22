module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisSubfieldConjStable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetTypeNormPrincipal
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
public import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.BaseField

section ext

variable {K K' : Type} [Field K] [Field K'] (f : K →+* K')

end ext

section host

variable {R : Ranks} (H : Host R)


end host

theorem isAlgebraic_exp (N : ℕ) : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I / N)) := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · simpa using isAlgebraic_one
  · exact ((Complex.isPrimitiveRoot_exp N h.ne').isIntegral h).tower_top.isAlgebraic

theorem exists_gens (E : Type) [Field E] [NumberField E] : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ K : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ K) → ∀ (τ : E →+* ℂ) x, τ x ∈ K := by
  classical
  let b := Module.finBasis ℚ E
  refine ⟨Finset.univ.image fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2), ?_, ?_⟩
  · intro z hz
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (b p.2)).algHom p.1.toRatAlgHom
  · intro K hK τ x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact K.smul_mem (hK _ (Finset.mem_image.2 ⟨(τ, i), Finset.mem_univ _, rfl⟩))

end GlobalTheory.Mem.BaseField

end
