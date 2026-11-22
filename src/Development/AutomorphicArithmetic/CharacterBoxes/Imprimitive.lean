module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
public import Development.AutomorphicArithmetic.CharacterBoxes.HalfPlane

@[expose] public section

open Formalism.HC

theorem UpperTheory.Top.imprimitive :
    ZeroFreeAll → ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ), 1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  intro h N _ χ s hs hχs
  have : NeZero χ.conductor := (PChar.of χ).ne
  have hL : DirichletCharacter.LFunction χ.primitiveCharacter s ≠ 0 := h (PChar.of χ) trivial s hs
  have hχ' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with hχ | hs1
    · left
      intro h1
      apply hχ
      rw [← χ.changeLevel_primitiveCharacter, h1, DirichletCharacter.changeLevel_one]
    · exact Or.inr hs1
  have hrw := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hχ'
  rw [χ.changeLevel_primitiveCharacter] at hrw
  rw [hrw]
  exact mul_ne_zero hL <| Finset.prod_ne_zero_iff.mpr fun p hp =>
    Claim.factor_ne_zero χ.primitiveCharacter (lt_trans (by norm_num) hs) p
      (Nat.prime_of_mem_primeFactors hp)
