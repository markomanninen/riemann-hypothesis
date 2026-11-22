module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
public import GroundTheory.AutomorphicForms.Iwasawa
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApplyMemTwKerOfNormalizer
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.EmbedsLevelZeroDepthZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Basics
variable {m : ℕ}






end Basics

section Mask
variable {N : ℕ} (P : Fin N → Fin N → Prop) [DecidableRel P]

def maskM (X : Matrix (Fin N) (Fin N) k) : Matrix (Fin N) (Fin N) k := fun a b => if P a b then X a b else 0

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem maskM_mul (hP : ∀ a b c, P a b → P b c → False) (X Y : Matrix (Fin N) (Fin N) k) :
    maskM P X * maskM P Y = 0 := by
  ext a c
  simp only [Matrix.mul_apply, maskM, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases h1 : P a b
  · by_cases h2 : P b c
    · exact (hP a b c h1 h2).elim
    · simp [h2]
  · simp [h1]


def U (hP : ∀ a b c, P a b → P b c → False) (X : Matrix (Fin N) (Fin N) k) : GL (Fin N) k :=
  ⟨1 + maskM P X, 1 - maskM P X, by simp [add_mul, mul_sub, maskM_mul P hP],
    by simp [sub_mul, mul_add, maskM_mul P hP]⟩






end Mask

section Rep
variable {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]


end Rep

section Parab
variable {M : ℕ}




end Parab

section Main

end Main

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
