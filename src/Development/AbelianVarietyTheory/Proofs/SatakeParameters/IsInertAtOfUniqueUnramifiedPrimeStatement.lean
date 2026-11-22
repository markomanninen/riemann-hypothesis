module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertAtOfUniqueUnramifiedPrime
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.SatakeDualWeyl.StatementG
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers

@[expose] public section

open IsDedekindDomain NumberField Formalism.UG GlobalTheory.SelfDualGenus
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isInertAt_of_unique_unramified_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (P : HeightOneSpectrum (𝓞 E)), (∀ x : 𝓞 E, x ≠ 0 → (x ∈ P.asIdeal ↔ (x : E)⁻¹ ∉ semiLoc v)) → (∃ x : 𝓞 (maximalRealSubfield E), ∃ y : 𝓞 E, (y : E) = algebraMap (maximalRealSubfield E) E (x : maximalRealSubfield E) ∧ y ∈ P.asIdeal ∧ y ∉ P.asIdeal ^ 2) → IsInertAt (maximalRealSubfield E) E v P := by
  first | exact @GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified | exact GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified | (intros; apply GlobalTheory.SelfDualGenus.isInertAt_of_unique_unramified <;> assumption)
