module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

@[expose] public section

namespace GlobalTheory.LocAsm

def exOne {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) : ∀ b, X b → ℂ := fun b x =>
  match b, x with
  | .ex _ _, _ => 1
  | .theta i j, x => φ (.theta i j) x

@[simp] theorem exOne_theta {X : GlobalTheory.SplitFlip.Edge → Type} (φ : ∀ b, X b → ℂ) (i j : ℕ) (x : X (.theta i j)) :
    exOne φ (.theta i j) x = φ (.theta i j) x := rfl

end GlobalTheory.LocAsm
