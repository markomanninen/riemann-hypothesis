module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints

open GlobalTheory.Grid GlobalTheory.Doubling

variable {D : D7}

def adj (S T : HSp D) (y : WO S T) : WO T S :=
  HMul.hMul (HMul.hMul ((S.gram⁻¹).map (incA D)) ((y : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D)).transpose)
    (T.gram.map (incA D))

def blkL (M V V₁ : HSp D) (z : WO M (hsum V V₁)) : WO M V := fun a b => z (Fin.castAdd V₁.rank a) b

def blkR (M V V₁ : HSp D) (z : WO M (hsum V V₁)) : WO M V₁ := fun a b => z (Fin.natAdd V.rank a) b

def ten (M V V₁ : HSp D) : (WO M V → ℂ) →ₗ[ℂ] (WO V₁ M → ℂ) →ₗ[ℂ] (WO M (hsum V V₁) → ℂ) :=
  LinearMap.mk₂ ℂ (fun φ φ' z => φ (blkL M V V₁ z) * φ' (adj M V₁ (blkR M V V₁ z)))
    (fun _ _ _ => funext fun _ => add_mul _ _ _) (fun _ _ _ => funext fun _ => mul_assoc _ _ _)
    (fun _ _ _ => funext fun _ => mul_add _ _ _) (fun _ _ _ => funext fun _ => mul_left_comm _ _ _)

section Route

variable (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (ε : Bool) (V M V₁ : Node D)

abbrev Pair : Type := (WO M.V V.V → ℂ) × (WO V₁.V M.V → ℂ)

def IsFinPair (f : Pair V M V₁) : Prop := IsFinVec ψ θ ε M V f.1 ∧ IsFinVec ψ θ (!ε) V₁ M f.2

variable {V M V₁}

def route (a : ArrS M V) (b : ArrS V₁ M) (mV : V.MeasDat) (mM : M.MeasDat) {n : ℕ} (Φ : Fin n → Pair V M V₁)
    (F : GA D V.V → ℂ) : GA D V₁.V → ℂ :=
  ∑ k, b.int mM (Φ k).2 (a.int mV (Φ k).1 F)

end Route

section Quot

variable (θ : InfFam D)

def IsDer (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ)) (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ)
    (Φ Φ' : Z → ℂ) : Prop :=
  ∀ z, HasDerivAt (fun t : ℝ => ρ (oneP θ X τ Y t) Φ z) (Φ' z) 0

def IsStable (X : HSp D) {Z : Type} (ρ : GA D X → Module.End ℂ (Z → ℂ)) (S : Submodule ℂ (Z → ℂ)) : Prop :=
  (∀ g ∈ GfC X, ∀ Φ ∈ S, ρ g Φ ∈ S) ∧ ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ S, ∃ Φ' ∈ S, IsDer θ X ρ τ Y Φ Φ'

def IsIrred (X : HSp D) (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi)
    (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi) : Prop :=
  Nontrivial Pi ∧ ∀ N : Submodule ℂ Pi, (∀ g ∈ GfC X, ∀ x ∈ N, rf g x ∈ N) → (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, rl τ Y x ∈ N) →
    N = ⊥ ∨ N = ⊤

structure IsCoinvMap {M X : HSp D} (ω : WRep M X) (S : Submodule ℂ (WO M X → ℂ)) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi) : Prop where

  stabM : IsStable θ M (fun g => ω (g, 1)) S

  stabX : IsStable θ X (fun h => ω (1, h)) S

  onto : S.map p = ⊤

  invf : ∀ g ∈ GfC M, ∀ Φ ∈ S, p (ω (g, 1) Φ) = p Φ

  invl : ∀ τ, ∀ Y ∈ lieAt M τ, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ M (fun g => ω (g, 1)) τ Y Φ Φ' → p Φ' = 0

  eqf : ∀ h ∈ GfC X, ∀ Φ ∈ S, p (ω (1, h) Φ) = rf h (p Φ)

  eql : ∀ τ, ∀ Y ∈ lieAt X τ, ∀ Φ ∈ S, ∀ Φ' ∈ S, IsDer θ X (fun h => ω (1, h)) τ Y Φ Φ' → p Φ' = rl τ Y (p Φ)

end Quot

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)


variable (R) in
def al (t : T) (i j : ℕ) : (AE D)ˣ →* Circle := R.toLevCh.mu t (j + 1) * R.eta ^ (rkV D i j % 2)

def be (i j : ℕ) : (AE D)ˣ →* Circle := G.chi (D.R.m - i) * R.eta ^ (rkV D i j % 2)

def routeA (t : T) (i j : ℕ) {n : ℕ} (Φ : Fin n → Pair (G.V i (j + 1)) (G.V (i + 1) (j + 1)) (G.V (i + 1) j))
    (F : GA D (G.V i (j + 1)).V → ℂ) : GA D (G.V (i + 1) j).V → ℂ :=
  route (G.X i (j + 1)) (G.th t (i + 1) j) (G.meas t i (j + 1)) (G.meas t (i + 1) (j + 1)) Φ F

end GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints

end
