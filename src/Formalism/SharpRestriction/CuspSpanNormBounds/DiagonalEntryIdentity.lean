module

public import Formalism.SharpRestriction.CuspSpanNormBounds.WeightedMirrorLevelOperator

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.S.UnitaryLevelOperators

section Gauge

open Matrix MeasureTheory TensorProduct
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA

end Gauge

section LevelR

open Matrix MeasureTheory TensorProduct
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Parts

variable {B : Base E} {r : ℕ} (C : Ctx B r) (Γ : GCtx E r)

def lenI (B : Base E) : ℝ := sSup B.I - sInf B.I

def mid3 (B : Base E) : Set ℝ := Set.Icc (sInf B.I + lenI B / 3) (sSup B.I - lenI B / 3)

def wnormSq {n : ℕ} (wt : (Fin n → Fin 2) → B.Rho → ℂ) (x : Fin (r + 1) → ℂ) (v : (Fin n → Fin 2) → E) : ℝ :=
  ∑ s, ∑ᶠ ρ, ‖wt s ρ‖ * (B.hs (C.P ρ x (v s)) (C.P ρ x (v s))).re

end Parts

end LevelR

section Further

open Matrix MeasureTheory Filter Topology Polynomial
open scoped ContDiff
open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

def IsKFinCoefT {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  ∃ a ∈ UH (Hpk k r), ∃ b ∈ UH (Hpk k r), IsKFinCoefH σ (fun g => f (a * g * b))

section Lists

variable {m : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E]

end Lists

def headEl (k j r' : ℕ) (h : Matrix (Fin j) (Fin j) ℂ)
    (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    Matrix (Fin (2 * (j + r') + k + 1)) (Fin (2 * (j + r') + k + 1)) ℂ := fun p q =>
  if hq : q.val < j then
    (if hp : 2 * (j + r') + k + 1 - j ≤ p.val then h ⟨2 * (j + r') + k - p.val, by omega⟩ ⟨q.val, hq⟩ else 0)
  else if hq2 : q.val < 2 * r' + k + 1 + j then
    (if hp : j ≤ p.val ∧ p.val < 2 * r' + k + 1 + j then g ⟨p.val - j, by omega⟩ ⟨q.val - j, by omega⟩ else 0)
  else
    (if hp : p.val < j then (hᴴ)⁻¹ ⟨p.val, hp⟩ ⟨2 * (j + r') + k - q.val, by omega⟩ else 0)

def levOf {k0 r : ℕ} (L : LocBessel (k0 + 1) r) (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) : Lev where
  k0 := k0
  r := r
  z := L.z
  z' := L.z'
  Wp := L.Wp
  Wq := L.Wq
  π := L.π
  π' := L.π'
  μsec := μsec

def cutF {k r : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (z z' : Fin (2 * r + k + 1) → ℂ)
    (χ : ℝ → ℝ) (ε : ℝ) (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → V :=
  fun g => ((χ (Gf k r z z' g / ε) : ℝ) : ℂ) • F g

def Std (D : Formalism.BasicNotions.D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (L : LocBessel (k0 + 1) D.R.rS)
    (μsec : ℂ → Matrix (Fin (k0 + 1 + 1)) (Fin (k0 + 1 + 1)) ℂ) (I : Set ℝ) : Prop :=
  (∀ i, L.ε i = epsSH D.R (Fin.cast (by rw [hk]) i)) ∧ L.c = cStd ∧
    IsSection (k0 + 1) D.R.rS L.z L.z' μsec ∧ IsCutS L.u L.u' I ∧
    ∃ ρ : Fin k0 → ℝ, Interlace L.u ρ ∧ Interlace L.u' ρ

abbrev Msq (s : ℕ) := Fin s → Fin s → ℂ

end Further

end Formalism.MainNotions.S.UnitaryLevelOperators
