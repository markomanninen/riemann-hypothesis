module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
public import Development.AbelianVarietyTheory.Definitions.Foundations.Letter
public import Development.AbelianVarietyTheory.Definitions.Foundations.ShCocOn
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

@[expose] public section

noncomputable section

open scoped MatrixGroups Matrix
open Filter
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV

namespace GlobalTheory.K4

open GlobalTheory.KZ ReciprocityTheory.Gal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def liftK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ)
    (a : X.Kl l ⧸ ((idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Kl l)))) : X.Khat l :=
  Classical.epsilon fun b : X.Khat l => AdicCompletion.eval (idl l) (X.Kl l) n b = a


open Classical in
def clsK (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (w : X.K) : X.Khat l :=
  if h : w ≠ 0 then liftK X l n (X.cls l n (Units.mk0 w h)) else 0

def liftSL (M : ℕ) (g : SL(2, ZMod M)) : SL(2, ℤ) :=
  Classical.epsilon fun γ : SL(2, ℤ) => Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ = g


def repC (l : ℕ) [Fact l.Prime] (r : ℕ) (x : (ZMod (l ^ r))ˣ) : Ω ≃ₐ[ℚ] Ω :=
  Classical.epsilon fun s : Ω ≃ₐ[ℚ] Ω => cycMod (F := ℚ) (Ω := Ω) l r s = x

def chik4 (l : ℕ) [Fact l.Prime] (e : ℕ) (ψ : ZMod l → Qbar l) (r : ℕ) (y : (ZMod (l ^ r))ˣ) : Qbar l :=
  ((((y : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * ψ (((y : ZMod (l ^ r)).val : ℕ) : ZMod l)

end GlobalTheory.K4
