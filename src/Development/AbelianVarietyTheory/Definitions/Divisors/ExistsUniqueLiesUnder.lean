module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NormDetAtConstOfPlacewise
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DegFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToShimXEqShimXOfPkg
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreimageConnectedComponentMem

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4

namespace GlobalTheory.Mean4O

section Comb

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

def lnAdl (A : Adl C Y) (σ : F →+* ℂ) (z : Pts Y σ) : ℝ :=
  lnN (A.m σ) (genAt A.D (under z)) z - (A.n : ℕ) * A.ci (InfinitePlace.mk σ)

end Comb

section Base

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag)

def LiesUnder (k : s.Comp) (y : Pt s) (x : (Φ.C k).Y.X) : Prop :=
  ∃ p : Sp Qb ⟶ (Φ.C k).Y.X, p ≫ (Φ.C k).π = y.y ∧ (Φ.C k).Carries p y.frame ∧ below p = x

def baseOn (k : s.Comp) (y : Pt s) : (Φ.C k).Y.X := Classical.epsilon (LiesUnder Φ k y)

abbrev basePt (y : Pt s) : (Φ.C (compPt s y)).Y.X := baseOn Φ (compPt s y) y

variable {Φ}

theorem LiesUnder.compPt_eq {k : s.Comp} {y : Pt s} {x : (Φ.C k).Y.X} (h : LiesUnder Φ k y x) : compPt s y = k := by
  obtain ⟨p, hp, -, -⟩ := h
  let o : Sp Qb := IsLocalRing.closedPoint Qb
  refine (PtComp.existsUnique_onComp s (y.y o)).unique (PtComp.onComp_compPt s y o) ?_
  obtain ⟨z, hz⟩ : ((s.U κ.σ₀).X k).dom.Nonempty := GlobalTheory.OrbitScalar.exists_mem_dom _
  refine ⟨⟨z, hz⟩, fun pt => ?_⟩
  exact (isPreconnected_range (Φ.C k).π.continuous).subset_connectedComponent ⟨p o, by rw [← hp]; rfl⟩
    (Φ.label k ⟨z, hz⟩ pt)


variable (Φ) in
theorem existsUnique_liesUnder (y : Pt s) : ∃! x, LiesUnder Φ (compPt s y) y x := by
  have : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  obtain ⟨⟨k, p⟩, hp, hu⟩ := Φ.lifts Qb y.fK y.y y.y_over y.frame
  obtain rfl : compPt s y = k := LiesUnder.compPt_eq ⟨p, hp.1, hp.2, rfl⟩
  refine ⟨below p, ⟨p, hp.1, hp.2, rfl⟩, ?_⟩
  rintro _ ⟨q, h₁, h₂, rfl⟩
  rw [eq_of_heq (Sigma.mk.inj (hu ⟨_, q⟩ ⟨h₁, h₂⟩)).2]


variable (Φ) in
theorem liesUnder_basePt (y : Pt s) : LiesUnder Φ (compPt s y) y (basePt Φ y) :=
  Classical.epsilon_spec (existsUnique_liesUnder Φ y).exists

end Base

section Roots

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def rootEx (τ : E →+* ℂ) (i : ℕ) : Letter Dw → ℤ := expo Dw (rootSym Dw (fun _ => false) none τ i)


open Classical in
theorem expo_single (a : Sym E) (n : ℤ) (x : Letter Dw) :
    expo Dw (Finsupp.single a n) x = if letterOf Dw a.2.2 = some x then n else 0 :=
  Finsupp.sum_single_index (by simp)

end Roots

structure MetIn {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (Φ : s.Flag) : Type where

  hm : ∀ k, Mets (Φ.C k) (cxSt D.what₂.LL)

  h0 : ∀ k σ (n : Letter S.Dw → ℤ), (cxSt D.what₂.LL).Met (Φ.C k).Y σ (divOf (Φ.C k) n)

  r : ∀ k σ, Pts (Φ.C k).Y σ → ℝ

  ab : ∀ k, Adl (cxSt D.what₂.LL) (Φ.C k).Y

  dir : D.what₂.Tau → Fin N → ℝ

  reg : ∀ k σ, (D.what₂.Tau → Fin N → ℝ) → ℝ → Pts (Φ.C k).Y σ → ℝ

structure Setup (D : D7) : Type 1 where

  A : Amb D

  N : ℕ

  j : ℕ
  indef : 1 ≤ j ∧ j < N

  S : Sig A N j

  κ : Lv A

  s : FinalTheorems S κ

  L : CmList A

  Φ : s.Flag
  dim_eq : ∀ k, (Φ.C k).Y.dim = Formalism.DegreeFormula.dimFl D.what₂.Tau N

  B : s.Bd L

  fl : s.Comp → D.what₂.Tau → ℂˣ

  Mb : ℝ → (D.what₂.Tau → Fin N → ℝ) → ℚ → ∀ k, Adl (cxSt D.what₂.LL) (Φ.C k).Y

  jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)

  ng : NgPkg

  loc : LocSt D N j ng

  glob : GlobSt fun p => (loc.loc p).Mdl

  adm : AdmSt D N j jC

  met : MetIn Φ

namespace Setup

variable {D : D7} (O : Setup D)

def pad : PadPkg D O.N O.j O.s.Comp O.jC O.ng :=
  padAt O.s O.loc O.glob O.adm (flatSt O.s O.Φ O.met.hm) (arIn O.s O.Φ O.met.hm)

def kit (key : KeySec O.s.Xo O.κ.c) : Kit O.s O.L (cxSt D.what₂.LL) O.jC O.ng :=
  ⟨O.Φ, O.dim_eq, key, O.B, O.fl, O.Mb, O.pad, fun _ => Iff.rfl⟩

def Y : DV.ShimX D.what₂.Tau :=
  shimXOfPkg (O.s.cx O.L O.B O.fl) (O.s.alg O.L (cxSt D.what₂.LL) (cutSt _) (resSt _) O.Φ O.dim_eq O.Mb) O.pad O.indef
    O.κ.primes fun _ hp => Nat.prime_of_mem_primeFactors hp

abbrev var (c : O.s.Comp) : Var D.what₂.LL := (O.Φ.C c).Y

abbrev ex (x : DV.Rt D.what₂.Tau O.N) : Letter O.S.Dw → ℤ := rootEx O.S.Dw (DV.tauEmb D x.1) x.2

def adl0 (c : O.s.Comp) (w : Sym D.host.E →₀ ℤ) : Adl (cxSt D.what₂.LL) (O.var c) :=
  adlOf (O.Φ.C c) (fun _ => O.met.h0 c) w

def htWt {c : O.s.Comp} (ρ : DV.Rt D.what₂.Tau O.N → Adl (cxSt D.what₂.LL) (O.var c)) (u : D.what₂.Tau → Fin O.N → ℝ)
    (z : (O.var c).X) : ℝ := -∑ x, u x.1 x.2 * (ρ x).ht z

def chg (c : O.s.Comp) (R : Option ℝ) (u : D.what₂.Tau → Fin O.N → ℝ) (σ : D.what₂.LL →+* ℂ) (z : Pts (O.var c) σ) : ℝ :=
  ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * lnRatio (O.met.hm c R σ (O.ex x)) (O.met.h0 c σ (O.ex x)) z

structure LatModel (P : Finset ℕ) (c : O.s.Comp) : Type 1 where

  V : Cover (O.var c)

  line : Finset ℕ → ((D.host.E →+* ℂ) × ℕ) ⊕ ℕ → HermLB V.p
  line_spec : ∀ Q ⊆ P, ∀ st, (letterOf O.S.Dw st).isSome →
    V.Induces (O.adl0 c (Finsupp.single (ArIn.ind Q, none, st) 1)) (line Q st) 1

  k : ℕ
  k_pos : 0 < k

  amp : HermLB V.p
  amp_spec : V.Induces (O.met.ab c) amp k

namespace LatModel

variable {O} {P : Finset ℕ} {c : O.s.Comp} (W : O.LatModel P c)

end LatModel

end Setup

end GlobalTheory.Mean4O
