module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TowU

section Coord

variable {R : Type} [CommRing R] {κ κ₁ : Type}

variable [Fintype κ] [Fintype κ₁] {W W₁ : Type} [AddCommGroup W] [Module R W] [AddCommGroup W₁] [Module R W₁]
  {B : W → W → R} {B₁ : W₁ → W₁ → R}

end Coord

section Frame

variable {R : Type} [CommRing R] {A : Type} [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α α₁ ν : Type} [Fintype α] [DecidableEq α] [Fintype α₁] [DecidableEq α₁] [Fintype ν] [DecidableEq ν]

structure IsFrame (J : Matrix α α A) (C D : Matrix α ν A) (ι : Matrix α α₁ A) : Prop where
  cc : Cᵀ * J * C.map c = 0
  dd : Dᵀ * J * D.map c = 0
  cd : Cᵀ * J * D.map c = 1
  ic : ιᵀ * J * C.map c = 0
  ci : Cᵀ * J * ι.map c = 0
  id : ιᵀ * J * D.map c = 0
  di : Dᵀ * J * ι.map c = 0
  basis : ∃ M : Matrix ((ν ⊕ ν) ⊕ α₁) α A, Matrix.fromCols (Matrix.fromCols C D) ι * M = 1 ∧
    M * Matrix.fromCols (Matrix.fromCols C D) ι = 1

end Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


def IsRat {α β κ : Type} [Fintype κ] {B : Matrix α β (AE F E) → Matrix α β (AE F E) → AF F} (d : Darboux B κ) : Prop :=
  ∀ x : Matrix α β E, ∃ y z : κ → F, d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

variable (σ : E →ₐ[F] E)

variable {σ}


end GlobalTheory.TowU

end
