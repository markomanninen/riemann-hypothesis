module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.InclRAlgebraMap
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.StLamOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnitaryOrbits.LocalSum
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem unitChoice_of_isArtinianRing_isReduced :
    ∀ (R : Type) [CommRing R] [IsArtinianRing R] [IsReduced R], PIW.AdelicOrbitU.UnitChoice R := by
  intro R _ _ _ k f hf
  classical
  let φ := IsArtinianRing.equivPi R
  have hex : ∀ I : MaximalSpectrum R, ∃ i, φ (f i) I ≠ 0 := by
    intro I
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    haveI : I.asIdeal.IsMaximal := I.isMaximal
    let ψ : R →+* R ⧸ I.asIdeal :=
      (Pi.evalRingHom (fun J : MaximalSpectrum R => R ⧸ J.asIdeal) I).comp φ.toRingHom
    have hle : Ideal.span (Set.range f) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact (RingHom.mem_ker).2 (h i)
    rw [hf] at hle
    have h1 : ψ 1 = 0 := (RingHom.mem_ker).1 (hle Submodule.mem_top)
    rw [map_one] at h1
    exact one_ne_zero h1
  choose c hc using hex
  let E : Fin k → ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal := fun i I => if c I = i then 1 else 0
  refine ⟨fun i => φ.symm (E i), ?_, ?_, ?_, ?_⟩
  · intro i
    rw [← map_mul]
    apply congrArg φ.symm
    funext I
    by_cases h : c I = i <;> simp [Pi.mul_apply, E, h]
  · intro i j hij
    rw [← map_mul, ← map_zero φ.symm]
    apply congrArg φ.symm
    funext I
    by_cases hi : c I = i
    · simp [Pi.mul_apply, E, hi, hij]
    · simp [Pi.mul_apply, E, hi]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← map_sum, ← map_one φ.symm]
      apply congrArg φ.symm
      funext I
      simp [Finset.sum_apply, E]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← isUnit_map_iff φ, map_sum, Pi.isUnit_iff]
      intro I
      have hcomp : (∑ i, φ (φ.symm (E i) * f i)) I = φ (f (c I)) I := by
        simp only [map_mul, AlgEquiv.apply_symm_apply, Finset.sum_apply, Pi.mul_apply, E, ite_mul,
          one_mul, zero_mul, Fintype.sum_ite_eq]
      rw [hcomp]
      haveI : I.asIdeal.IsMaximal := I.isMaximal
      letI := Ideal.Quotient.field I.asIdeal
      exact isUnit_iff_ne_zero.2 (hc I)

end GlobalTheory.CompanionTheory.SW
