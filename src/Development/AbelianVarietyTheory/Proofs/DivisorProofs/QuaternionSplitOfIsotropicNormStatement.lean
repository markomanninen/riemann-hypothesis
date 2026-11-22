module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionSplitOfIsotropicNorm
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_split_of_isotropic_norm : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) → ∃ φ : ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F, ∀ x, (φ x).det = nrm x := by
  first | exact @GlobalTheory.quaternion_split_of_isotropic | exact GlobalTheory.quaternion_split_of_isotropic | (intros; apply GlobalTheory.quaternion_split_of_isotropic <;> assumption)
