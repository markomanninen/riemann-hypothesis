module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.DisjointSplitLevelPlaces
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IntFormsSubset
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl

@[expose] public section

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.IndefR.NX
open scoped TensorProduct
open Classical

namespace GlobalTheory.TowerCov

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsLevN (E : ExpSet D) (N : ℕ) : Prop :=
  N ≠ 0 ∧ (∀ p : ℕ, p.Prime → p ∣ N →
    p ≠ 2 ∧ Nat.Coprime p E.l ∧ (∀ a, p ≠ E.pde a) ∧ (∀ a, p ≠ E.gp a) ∧ D.host.cls p = .splitK ∧
      ¬ p ∣ Ideal.absNorm D.host.ccK) ∧ Squarefree N

def LevN (E : ExpSet D) : Type := {N : ℕ // IsLevN E N}

section Fields

variable (E : ExpSet D) {O : Type} [CommRing O] (C : CoefLat E O) (Base : Set (GA D E.W → ℂ))
  (LQ : LevN E → Subfield ℂ) (Rat : ∀ N : LevN E, Submodule (LQ N) (GA D E.W → ℂ))
  (Λ : Subring ℂ) (BaseInt : Submodule Λ (GA D E.W → ℂ)) (Int : LevN E → Submodule Λ (GA D E.W → ℂ))

variable {E C Base LQ Rat Λ BaseInt Int}

end Fields

section Covers

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.CoverRead

variable {E : ExpSet D} {T : CoreJ D} {j : ℕ} {σ : T.Q.c.F →+* ℂ} (hV : T.V j σ = E.W)
  (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (z : ℂ)

def placesIn {L : Type} [Field L] [NumberField L] (ι : L →+* ℂ) (Λ : Subring ℂ) : Set (HeightOneSpectrum (𝓞 L)) :=
  {la | ∀ x : L, la.valuation L x ≤ 1 → ι x ∈ Λ}

end Covers

end GlobalTheory.TowerCov
