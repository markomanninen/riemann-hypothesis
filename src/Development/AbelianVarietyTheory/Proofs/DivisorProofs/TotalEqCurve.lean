module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt
open GlobalTheory.VBExt (AdaptedChart)
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.MixDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D d : ℕ}

def part (ρ : AlgChart p σ D → CxPts p σ → ℝ) : Measure (CxPts p σ) :=
  ChartGlue.glueMeas (fun c : AlgChart p σ D => c.e) fun c y => ENNReal.ofReal (ρ c y)

def IsDens (ρ : AlgChart p σ D → CxPts p σ → ℝ) : Prop :=
  (∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    ρ c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * ρ c' y) ∧
  ∀ c : AlgChart p σ D, ContinuousOn (fun v => ρ c (c.e.symm v)) c.e.target

variable {ρ ρ' : AlgChart p σ D → CxPts p σ → ℝ}

def transMat (c c' : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun a b => fderiv ℂ (c'.e ∘ c.e.symm) (c.e y) (EuclideanSpace.single b 1) a

def IsForm (M : AlgChart p σ D → CxPts p σ → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  (∀ (c c' : AlgChart p σ D) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    M c y = chg (transMat c c' y) (M c' y)) ∧
  (∀ c : AlgChart p σ D, ContinuousOn (fun v => M c (c.e.symm v)) c.e.target) ∧
  ∀ c : AlgChart p σ D, ∀ y ∈ c.e.source, (M c y).IsHermitian

variable {A M M' J : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}

def chernMat {B : LB X} (φ : Weight p σ B) (c : AlgChart p σ D) (y : CxPts p σ) : Matrix (Fin D) (Fin D) ℂ :=
  c.hess φ (pick φ.isLB y) y

theorem chernMat_congr {L N : HermLB p} (e : L.Isometric N) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : chernMat (L.φ σ) c y = chernMat (N.φ σ) c y := by
  unfold chernMat
  exact (e.hess_eq c hy (mem_pick _ y) (mem_pick _ y)).symm

section Flag

variable {E : X.Modules} {r : ℕ} (h : VMetric p E r) (fl : Vert.Flag E r)

end Flag

section Cell

variable {ι : Type} [Fintype ι] {r : ι → ℕ} (e : Fin (d + 1) ≃ Option (Σ a, Low (r a)))



def emb {m : ℕ} (i : Fin m) : Fin i ⊕ Fin 1 → Fin m := Sum.elim (Fin.castLE i.isLt.le) fun _ => i



variable {m : ℕ}

variable {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)

end Cell

end GlobalTheory.MixDens
