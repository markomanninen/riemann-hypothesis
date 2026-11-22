module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigCongr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColumnCharacterEigenSubmoduleNeBotStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviWhittakerColumnCharacterEigenVecMulNeBotStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockTriVecMulEqSinglePredStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCommOfIrreducibleMultiplicityLeOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCommonFixedLeOneOfCommutingHeckeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOneStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeOne

@[expose] public section

noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module Matrix

variable {F : Type} [Field F] {r : ℕ}

section Nonvanishing

variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}

end Nonvanishing

section Embedding

variable {d d' : ℕ}

variable (b : Fin r → ℕ) (c : ℕ)

end Embedding

section Main

variable {V : Type} [AddCommGroup V] [Module ℂ V] {b : Fin r → ℕ}

theorem leviWh_eq_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
    (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → leviWh ψ b σ = 1 := by
  first
  | exact @_root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one
  | exact _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one
  | (apply _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BlockDecompositionExistence.leviWh_eq_one ..)

end Main

end GlobalTheory.FinGL.LeviWh
