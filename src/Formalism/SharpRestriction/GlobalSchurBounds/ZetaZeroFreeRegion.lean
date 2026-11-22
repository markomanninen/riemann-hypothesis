module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationBoundaryCriterion
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions Finset
open scoped Pointwise ComplexConjugate

open Classical

abbrev Chr (D : D7) : Type := D.R.GG →* ℂˣ

def sgnC : ℤˣ →* ℂˣ := Units.map (Int.castRingHom ℂ).toMonoidHom

abbrev chC (D : D7) : Chr D := D.R.chC

def psC (D : D7) : Chr D := sgnC.comp D.R.chQ

def Unram (D : D7) (p : ℕ) : Prop := p.Prime ∧ ¬ ((p : ℤ) ∣ discr D.host.E)

def InertK (D : D7) (p : ℕ) : Prop :=
  p.Prime ∧ (D.host.cls p = PrimeClass.signal ∨ D.host.cls p = PrimeClass.inertClass)

def Reads (D : D7) (ψ : Chr D) (χ : Σ N : ℕ+, DirichletCharacter ℂ N) : Prop :=
  χ.2.IsPrimitive ∧ ∀ p : ℕ, Unram D p → χ.2 (p : ZMod χ.1) = ((ψ (frob D p) : ℂˣ) : ℂ)

def prim (D : D7) (ψ : Chr D) : Σ N : ℕ+, DirichletCharacter ℂ N :=
  if h : ∃ χ, Reads D ψ χ then h.choose else ⟨1, 1⟩

def Gc (D : D7) (ψ : Chr D) (y : ℝ) : ℂ := gChi (prim D ψ).2 y

def Lp (D : D7) (ψ : Chr D) : ℂ := logDerivativeAtOne (prim D ψ).2

def iner (D : D7) : D.R.GG := (sgc0, 1)

def askP (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) (p : ℕ) : ℝ :=
  ∑' i : ℕ, if 1 ≤ i ∧ frob D p ^ i ∉ D.R.Psi then
    max (a / (p : ℝ) ^ i - w (rho D τ (frob D p ^ i))) 0 else 0

def gD (D : D7) (i : ℕ) : D.R.GG :=
  if frob D D.host.d ^ i ∉ D.R.Psi then frob D D.host.d ^ i else frob D D.host.d ^ i * iner D

def askD (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) : ℝ :=
  ∑' i : ℕ, if 1 ≤ i then max (a / (D.host.d : ℝ) ^ i - w (rho D τ (gD D i))) 0 else 0

def ASKjt (D : D7) (a : ℝ) (w : D.R.GG → ℝ) (τ : D.R.GG) : ℝ :=
  (∑' p : ℕ, if InertK D p then 2 * Real.log p * askP D a w τ p else 0) +
    Real.log D.host.d * askD D a w τ

def adm5 (D : D7) (s : Scale) (c : ℝ) : Prop :=
  ∀ ψ : Chr D, ∀ y : ℝ, s.X' / 3 ≤ y → ‖Gc D ψ y‖ ≤ y * Real.exp (-(c * s.x ^ (s.eps / 8)))

def adm10 (D : D7) : Prop := ∀ ψ : Chr D, ∃ χ, Reads D ψ χ

def SizesAt (D : D7) (s : Scale) (δ : ℝ) : Prop :=
  s.x ^ (2 + 8 * s.eps - δ) ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ s.x ^ (2 + 8 * s.eps + δ) ∧
  (s.x * s.delta1) ^ ((1 : ℝ) / 2 - δ) ≤ (D.R.m : ℝ) ∧
    (D.R.m : ℝ) ≤ (s.x * s.delta1) ^ ((1 : ℝ) / 2 + δ) ∧
  s.x ^ ((9 : ℝ) / 2 + 10 * s.eps - δ) ≤ (D.R.k : ℝ) ∧
    (D.R.k : ℝ) ≤ s.x ^ ((9 : ℝ) / 2 + 10 * s.eps + δ)

end Formalism.MainNotions.ZetaZeroFreeRegion

end
