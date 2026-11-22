module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProdAbsNormDivsDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicHeckeCharValuesInNumberFieldStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharactersPrescribedValues
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBaseDataAdmissibleStatement
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition
public import Development.AutomorphicArithmetic.PrimeDiscriminants.ExistsPrimitiveRootTorsionOrder
public import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
public import Formalism.FrobeniusOrbits.HostThickExists
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.MuSplitsCfacts
public import Development.AutomorphicArithmetic.WeightCongruences.ProdResidueCharNormOneUnitEqOne

@[expose] public section

open UpperTheory.HF

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open Formalism.L2.Col

noncomputable section

namespace GlobalTheory.Mem.DatHecke

open Formalism.L2.Host (HChar embPsi)
open GlobalTheory.Mem.Chr (ConjPl CMData)

theorem exists_gen (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] :
    ∃ α : ℂ, IsAlgebraic ℚ α ∧ ∀ (K : Type) [Field K] [CharZero K] (σ : K →+* ℂ), (∃ x, σ x = α) →
      ∀ z ∈ M, ∃ x, σ x = z := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element ℚ M
  refine ⟨a, (Algebra.IsAlgebraic.isAlgebraic a).algHom M.val, ?_⟩
  intro K _ _ σ ⟨x, hx⟩ z hz
  have h1 : (⊤ : IntermediateField ℚ M) ≤ (σ.toRatAlgHom.fieldRange).comap M.val := by
    rw [← ha]
    exact IntermediateField.adjoin_simple_le_iff.2 ⟨x, hx⟩
  exact h1 (IntermediateField.mem_top (x := (⟨z, hz⟩ : M)))

section Host

variable {R : Ranks} (H : Host R)

end Host


section PrimesOk

variable {X : Fields} {Pr : Primes X}

theorem mem_vG (h : Pr.Ok) (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.E)) :
    w ∈ Pr.vG i ↔ X.conjO (Pr.piG i) ∈ w.asIdeal := by
  refine mem_divs (fun h0 => ?_) w
  have h1 := h.piG_norm i
  rw [h0, mul_zero] at h1
  have h2 : (Pr.g i : 𝓞 X.E) ≠ 0 := by exact_mod_cast (h.g_prime i).ne_zero
  exact h2 h1.symm

theorem mem_vGs (w : HeightOneSpectrum (𝓞 X.E)) : w ∈ Pr.vGs ↔ ∃ i, w ∈ Pr.vG i := by
  classical
  unfold Primes.vGs
  rw [Fin.exists_fin_two]
  convert Finset.mem_union

theorem g_mem_of_mem_vG (h : Pr.Ok) {i : Fin 2} {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ w.asIdeal := by
  rw [← h.piG_norm i]
  exact w.asIdeal.mul_mem_left _ ((mem_vG h i w).1 hw)

end PrimesOk

end GlobalTheory.Mem.DatHecke

end
