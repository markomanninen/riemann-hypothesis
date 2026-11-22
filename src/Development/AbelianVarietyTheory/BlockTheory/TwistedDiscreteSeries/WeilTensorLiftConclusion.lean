module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix

namespace GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsUnitaryCharacter (μ : kˣ →* ℂˣ) : Prop := IsSmoothChar μ ∧ IsUnitaryChar μ

def IsIrredUnitary {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) : Prop :=
  IsSmooth π ∧ π.IsIrreducible ∧ IsUnitarisable π

def SupportCondition {a : ℕ} (t : ℕ) (μ : kˣ →* ℂˣ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin a) k) V) : Prop :=
  ∀ j : ℕ, ¬ InSupport π (μ * absPow k (((t : ℂ) + 1) / 2 + j)) ∧
    ¬ InSupport π (μ * absPow k (-(((t : ℂ) + 1) / 2 + j)))



def invTranspose (n : ℕ) (R : Type) [CommRing R] : GL (Fin n) R →* GL (Fin n) R where
  toFun h := ⟨(h⁻¹ : GL (Fin n) R).valᵀ, h.valᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  map_one' := by
    apply Units.ext
    show ((1 : GL (Fin n) R)⁻¹ : GL (Fin n) R).valᵀ = 1
    rw [inv_one, Units.val_one, transpose_one]
  map_mul' x y := by
    apply Units.ext
    show ((x * y)⁻¹ : GL (Fin n) R).valᵀ = (x⁻¹ : GL (Fin n) R).valᵀ * (y⁻¹ : GL (Fin n) R).valᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul]


end GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorLiftConclusion
