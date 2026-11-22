module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DiagMemCongruencePairs

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob.Iota

variable {E : Type} [Field E] [NumberField E]
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}

open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in
private theorem one_le_inv_differentIdeal :
    (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ := by
  have h := FractionalIdeal.inv_anti_mono (K := E)
    (I := (↑(differentIdeal ℤ (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)) (J := 1)
    (by simp [differentIdeal_ne_bot]) FractionalIdeal.coeIdeal_le_one
  simpa using h


open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] in
theorem _root_.GlobalTheory.SgGlob.Iota.one_mem_dInv (j : ℕ) : (1 : E) ∈ _root_.GlobalTheory.SgGlob.dInv E j := by
  unfold _root_.GlobalTheory.SgGlob.dInv
  have hpow : (1 : FractionalIdeal (𝓞 E)⁰ E) ≤ (↑(differentIdeal ℤ (𝓞 E)))⁻¹ ^ j := by
    simpa using pow_le_pow_left' (one_le_inv_differentIdeal (E := E)) j
  exact hpow (FractionalIdeal.one_mem_one _)

section Pair

variable {g : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {P P' : Matrix (Fin n) (Fin (r + 1)) E}

end Pair

section Gram

end Gram

end GlobalTheory.SgGlob.Iota
