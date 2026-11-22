module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConstantOneMemNonvanishing
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB
open scoped ComplexConjugate

namespace GlobalTheory.CxForm

section Values

variable {n : ℕ}

def hermMat (α : Alt n) : Matrix (Fin n) (Fin n) ℂ :=
  of fun a b => -Complex.I * (bas n).repr α {a.castAdd n, b.natAdd n}

def eval₂ (α : Alt n) (ξ η : V n) : ℂ :=
  Complex.I * (HermFrame.form (hermMat α) ξ η - HermFrame.form (hermMat α) η ξ)

end Values

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D D' : ℕ}

namespace ArRing

variable {B : BottChern} {h : IsRegVar p D} (R : ArRing B h) {r : ℕ} (E : HermVB p r)

end ArRing


variable (q) in
def IsGenSmooth (π : Y ⟶ X) : Prop :=
  ∃ U : Y.Opens, (∀ σ (y : CxPts q σ), y ∈ ptsIn q σ U) ∧ Smooth (U.ι ≫ π)

open Limits

def relCot (π : Y ⟶ X) : Y.Modules := Conormal.conormal (pullback.diagonal π)

def dRel (π : Y ⟶ X) (W : Y.Opens) (f : Γ(Y, W)) : Γ(relCot π, W) :=
  Conormal.d (pullback.diagonal_fst π) (V := W) (W := pullback.snd π π ⁻¹ᵁ W)
    (by rw [← Scheme.Hom.comp_preimage, pullback.diagonal_snd]; exact le_rfl) ((pullback.snd π π).app W f)


variable (q) in
def IsRelAcyclic (π : Y ⟶ X) (L : LB Y) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (W : κ → Y.Opens),
    (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = π ⁻¹ᵁ U → ∀ n, (AbLaw.cechLB q L W).ExactAt (n + 1)

end GlobalTheory.CxForm
