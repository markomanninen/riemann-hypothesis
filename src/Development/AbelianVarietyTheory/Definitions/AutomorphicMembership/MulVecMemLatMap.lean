module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndepOfGqNeZero
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMassConst
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

section Tri

variable {m : ℕ} {u v : Matrix (Fin m) (Fin m) E}

theorem up_one : IsUp (1 : Matrix (Fin m) (Fin m) E) :=
  fun _ _ => ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq _⟩

def IsStrict (A : Matrix (Fin m) (Fin m) E) : Prop := ∀ i j, j ≤ i → A i j = 0

def simpleSum {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E := ∑ a : Fin r, A a.castSucc a.succ

end Tri

section Frames

variable {σ : E →+* E} {n r : ℕ} {J s : Matrix (Fin n) (Fin n) E} {P P' : Matrix (Fin n) (Fin (r + 1)) E}
  {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}

end Frames

section Lattices

variable [NumberField E] {σ : E →+* E} {n r : ℕ} {J s : Matrix (Fin n) (Fin n) E}
  {P P' : Matrix (Fin n) (Fin (r + 1)) E} {u v : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
  {Λ M : Submodule (𝓞 E) (Fin n → E)}





end Lattices

end GlobalTheory.IntTerm
