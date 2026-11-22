module

public import Mathlib
public import ReciprocityTheory.DualLattices.HtLinStatement

@[expose] public section

noncomputable section

open IsLocalRing TensorProduct ReciprocityTheory.PGsh

namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts

universe u v

section Eval

variable {A : Type*} {R : Type*} [CommRing A] [CommRing R] [Algebra A R] {σ : Type*}

def evalTerm (F : MvPowerSeries σ A) (x : σ → R) (d : σ →₀ ℕ) : R :=
  MvPowerSeries.coeff d F • d.prod fun i n => x i ^ n

theorem evalTerm_finite [Finite σ] (F : MvPowerSeries σ A) (x : σ → R)
    (hx : ∀ i, IsNilpotent (x i)) : (Function.support (evalTerm F x)).Finite := by
  classical
  choose N hN using hx
  haveI := Fintype.ofFinite σ
  refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm N)).subset fun d hd => ?_
  by_contra hcon
  apply hd
  have : ∃ i, N i < d i := by
    by_contra h
    push Not at h
    exact hcon fun i => by simpa using h i
  obtain ⟨i, hi⟩ := this
  have hi0 : i ∈ d.support := by
    rw [Finsupp.mem_support_iff]; omega
  unfold evalTerm
  have h0 : x i ^ d i = 0 := pow_eq_zero_of_le hi.le (hN i)
  rw [Finsupp.prod, Finset.prod_eq_zero (f := fun a => x a ^ d a) hi0 h0, smul_zero]

def evalNil [Finite σ] (F : MvPowerSeries σ A) (x : σ → R) (hx : ∀ i, IsNilpotent (x i)) : R :=
  ∑ d ∈ (evalTerm_finite F x hx).toFinset, evalTerm F x d

theorem evalNil_eq_finsum [Finite σ] (F : MvPowerSeries σ A) (x : σ → R)
    (hx : ∀ i, IsNilpotent (x i)) : evalNil F x hx = ∑ᶠ d, evalTerm F x d :=
  (finsum_eq_sum _ (evalTerm_finite F x hx)).symm

end Eval



variable {R₀ : Type u} [CommRing R₀]

structure ResAlg (k : LAlg R₀) where

  alg : LAlg R₀

  res : LHom alg k
  res_surj : Function.Surjective res.1
  res_ker : RingHom.ker res.1 = maximalIdeal (alg : Type u)

structure NilAlg (k : LAlg R₀) extends ResAlg k where
  nil : ∀ x ∈ maximalIdeal (alg : Type u), IsNilpotent x

variable {k : LAlg R₀}

abbrev Tors (B : BX R₀) (n : ℕ) (R : LAlg R₀) : AddSubgroup (B.G R) :=
  AddSubgroup.torsionBy (B.G R) n

structure TorsionRep (B : BX R₀) (p : ℕ) (O : ResAlg k) where

  A : Tors B p k → ResAlg k

  str : ∀ x, LHom O.alg (A x).alg
  str_res : ∀ x, (A x).res.comp (str x) = O.res

  y : ∀ x, Tors B p (A x).alg
  y_res : ∀ x, B.map (A x).res (y x : B.G (A x).alg) = (x : B.G k)
  universal : ∀ (S : LAlg R₀) (s : LHom O.alg S) (t : Tors B p S),
    ∃! c : Σ x : Tors B p k, LHom (A x).alg S,
      c.2.comp (str c.1) = s ∧ B.map c.2 (y c.1 : B.G (A c.1).alg) = (t : B.G S)

namespace TorsionRep

variable {B : BX R₀} {p : ℕ} {O : ResAlg k} (D : TorsionRep B p O)

variable (C : Type v) [Field C] [Algebra (O.alg : Type u) C]

end TorsionRep

end GlobalTheory.IndefiniteRowSideFullHecke.FormalGroupTorsionCharts
