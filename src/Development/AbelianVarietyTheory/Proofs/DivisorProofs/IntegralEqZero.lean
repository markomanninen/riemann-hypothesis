module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeInnerProductModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfChars
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAntiStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteCountableGQ
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat

@[expose] public section

namespace GlobalTheory.RowPartsOrth

section Generic
open MeasureTheory Formalism.IndefR.Bridge GlobalTheory.DoubleCosetAdjoint

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)

variable {μ Γ 𝓕}



theorem isDC_of_local {H : Type} [Group H] (J L : Subgroup H) (x : H) (A : Finset H) (hx : x ∈ L)
    (hs : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hL : ∀ a ∈ A, a ∈ L) (hA : IsDC (J ⊓ L) x A) : IsDC J x A := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨k₁, k₂, e⟩ := hA.1 a ha
    exact ⟨⟨k₁, k₁.2.1⟩, ⟨k₂, k₂.2.1⟩, e⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ha, b, hb, haL, e, hc⟩ := hs k₁ k₁.2
    have e2 : (k₁ : H) * x * k₂ = a * x * (b * k₂) := by
      rw [e, mul_assoc a b x, (hc x hx).eq]; simp only [mul_assoc]
    obtain ⟨r, ⟨hr, hr2⟩, hu⟩ := hA.2 (a * x) ⟨⟨a, ha, haL⟩, 1, by simp⟩
    rw [e2]
    refine ⟨r, ⟨hr, ?_⟩, fun r' hr' => hu r' ⟨hr'.1, ?_, ?_⟩⟩
    · have := J.mul_mem hr2.1 (J.mul_mem hb k₂.2)
      simpa only [mul_assoc] using this
    · have := J.mul_mem hr'.2 (J.inv_mem (J.mul_mem hb k₂.2))
      simpa [mul_assoc] using this
    · exact L.mul_mem (L.inv_mem (hL r' hr'.1)) (L.mul_mem haL hx)

end Generic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx NumberField IsDedekindDomain Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.RowPartsOrth
