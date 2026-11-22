module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitOfIsotropic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA.Split

variable {F : Type} [Field F]

end GlobalTheory.QSA.Split

namespace GlobalTheory

theorem quaternion_split_of_isotropic : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 →
    (∃ x : ℍ[F, a, b], x ≠ 0 ∧ nrm x = 0) →
    ∃ φ : ℍ[F, a, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F, ∀ x, (φ x).det = nrm x := by
  first
  | exact @_root_.GlobalTheory.MatrixHomBijective.split_of_isotropic
  | exact _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic
  | (apply _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic <;> assumption)
  | (intros; apply _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MatrixHomBijective.split_of_isotropic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MatrixHomBijective.split_of_isotropic ..)

end GlobalTheory
