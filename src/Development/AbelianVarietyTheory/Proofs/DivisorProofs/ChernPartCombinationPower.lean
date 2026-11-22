module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralIndependentOfCoefficient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open GlobalTheory.Points GlobalTheory.HermFrame
open scoped Classical

namespace GlobalTheory.ChernTop

variable {n : ℕ}

def rowForm (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] Ev n := Fintype.linearCombination ℂ fun b => sym (a, b)

def matForm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Ev n where
  toFun H := kappa • ∑ a, rowForm a (H a)
  map_add' H H' := by
    rw [← smul_add, ← Finset.sum_add_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_add _ _ _)
  map_smul' c H := by
    rw [RingHom.id_apply, smul_comm, Finset.smul_sum (r := c)]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_smul (rowForm a) c (H a))

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {σ : k →+* ℂ}

variable {c : AlgChart p σ D} {y : CxPts p σ}

end GlobalTheory.ChernTop
