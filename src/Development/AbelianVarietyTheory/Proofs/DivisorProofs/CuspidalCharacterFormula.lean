module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOrbitDegreeOverPrimeFieldFbar
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsTeichmullerMapAlgebraicClosureFiniteField

@[expose] public section

noncomputable section

namespace GlobalTheory.GoodCharsCompare

open Polynomial Formalism.CyclotomicNorms Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.CuspValueComparison

variable {g : ℕ} [Fact g.Prime]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_pow_dg_mul_eq_self (y : _root_.Formalism.CyclotomicNorms.Fbar g) (q : ℕ) :
    y ^ g ^ (_root_.GlobalTheory.GoodCharsCompare.dg y * q) = y := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.mul_succ, pow_add, pow_mul, ih, (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).1]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_dg_mul {d : ℕ} (hd : 0 < d) {y : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hy : y ^ (g ^ d - 1) = 1) : ∃ k, d = _root_.GlobalTheory.GoodCharsCompare.dg y * k := by
  have hDpos := _root_.GlobalTheory.GoodCharsCompare.dg_pos y
  have hd' : y ^ g ^ d = y := _root_.GlobalTheory.GoodCharsCompare.pow_g_of hy
  refine ⟨d / _root_.GlobalTheory.GoodCharsCompare.dg y, ?_⟩
  have hr : y ^ g ^ (d % _root_.GlobalTheory.GoodCharsCompare.dg y) = y ^ g ^ 0 := by
    rw [pow_zero, pow_one]
    conv_rhs => rw [← hd', ← Nat.div_add_mod d (_root_.GlobalTheory.GoodCharsCompare.dg y), pow_add, pow_mul,
      pow_pow_dg_mul_eq_self]
  have h1 := (_root_.GlobalTheory.GoodCharsCompare.frobenius_orbit_degreeOverPrimeFieldFbar y).2 _ (Nat.mod_lt _ hDpos) 0 hDpos hr
  have h2 := Nat.div_add_mod d (_root_.GlobalTheory.GoodCharsCompare.dg y)
  rw [h1, add_zero] at h2
  exact h2.symm

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
private theorem pow_pow_sub_one_eq_one_of_pow_pow_eq_self {y : _root_.Formalism.CyclotomicNorms.Fbar g} (hy : y ≠ 0) {n : ℕ}
    (h : y ^ g ^ n = y) : y ^ (g ^ n - 1) = 1 := by
  rw [← Nat.sub_add_cancel (Nat.one_le_pow n g (Fact.out : g.Prime).pos), pow_succ] at h
  exact mul_right_cancel₀ hy (h.trans (one_mul y).symm)

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.root_pow {ι : Type} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι (ZMod g)} (hM : M.det ≠ 0)
    {p : (ZMod g)[X]} {k : ℕ} (hp : Irreducible p) (hk : M.charpoly = p ^ k) {y : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hy : y ∈ _root_.Formalism.CyclotomicNorms.rootsBar M.charpoly) : y ^ (g ^ Fintype.card ι - 1) = 1 := by
  have hint := _root_.GlobalTheory.GoodCharsCompare.isInt y
  have hchar0 : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hchar0, ← coeff_zero_eq_aeval_zero',
      map_eq_zero] at hy
    apply hM
    rw [Matrix.det_eq_sign_charpoly_coeff, hy, mul_zero]
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    rw [hk, _root_.GlobalTheory.GoodCharsCompare.mem_rootsBar one_ne_zero, map_one] at hy
    exact one_ne_zero hy
  have hyp : aeval y p = 0 := by
    rw [_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hchar0, hk, map_pow] at hy
    exact (pow_eq_zero_iff hk0).mp hy
  have hdvd : minpoly (ZMod g) y ∣ p := minpoly.dvd _ _ hyp
  have hassoc : Associated (minpoly (ZMod g) y) p :=
    associated_of_dvd_dvd hdvd ((minpoly.irreducible hint).dvd_symm hp hdvd)
  have hdeg : p.natDegree = _root_.GlobalTheory.GoodCharsCompare.dg y :=
    (natDegree_eq_of_degree_eq (degree_eq_degree_of_associated hassoc)).symm
  have hcard : Fintype.card ι = _root_.GlobalTheory.GoodCharsCompare.dg y * k := by
    rw [← Matrix.charpoly_natDegree_eq_dim M, hk, natDegree_pow, hdeg, mul_comm]
  apply pow_pow_sub_one_eq_one_of_pow_pow_eq_self hy0
  rw [hcard]
  exact pow_pow_dg_mul_eq_self y k

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.coeff_zero_iff {f : (ZMod g)[X]} (hf : f ≠ 0) :
    f.coeff 0 ≠ 0 ↔ (0 : _root_.Formalism.CyclotomicNorms.Fbar g) ∉ _root_.Formalism.CyclotomicNorms.rootsBar f := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [mem_roots_map_of_injective (algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g)).injective hf, ← aeval_def,
    ← coeff_zero_eq_aeval_zero', map_eq_zero]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.squarefree_iff {f : (ZMod g)[X]} (hf : f ≠ 0) :
    Squarefree f ↔ (_root_.Formalism.CyclotomicNorms.rootsBar f).Nodup := by
  unfold _root_.Formalism.CyclotomicNorms.rootsBar
  rw [nodup_roots_iff_of_splits (Polynomial.map_ne_zero hf) (IsAlgClosed.splits _), separable_map,
    PerfectField.separable_iff_squarefree]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.primeToPart_map (β : _root_.Formalism.CyclotomicNorms.Fbar g ≃* _root_.Formalism.CyclotomicNorms.Fbar g) (l : ℕ) (x : _root_.Formalism.CyclotomicNorms.Fbar g) :
    _root_.Formalism.CyclotomicNorms.primeToPart l (β x) = β (_root_.Formalism.CyclotomicNorms.primeToPart l x) := by
  unfold _root_.Formalism.CyclotomicNorms.primeToPart
  rw [MulEquiv.orderOf_eq, map_pow]

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.eq_minpoly {φ : (ZMod g)[X]} (hm : φ.Monic)
    (hi : Irreducible φ) {x : _root_.Formalism.CyclotomicNorms.Fbar g} (hx : x ∈ _root_.Formalism.CyclotomicNorms.rootsBar φ) : φ = minpoly (ZMod g) x :=
  minpoly.eq_of_irreducible_of_monic hi
    ((_root_.GlobalTheory.GoodCharsCompare.mem_rootsBar hm.ne_zero).mp hx) hm

def Ext (ι : (_root_.Formalism.CyclotomicNorms.Fbar g)ˣ →* ℂˣ)
    (ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ) : Prop :=
  ∀ u : (_root_.Formalism.CyclotomicNorms.Fbar g)ˣ, ((ι u : ℂˣ) : ℂ) = ω u

open Polynomial in
variable {g : ℕ} [Fact g.Prime] in
theorem _root_.GlobalTheory.GoodCharsCompare.exists_ext {ι : (_root_.Formalism.CyclotomicNorms.Fbar g)ˣ →* ℂˣ}
    (hι : Function.Injective ι) :
    ∃ ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ, Function.Injective ω ∧ _root_.GlobalTheory.GoodCharsCompare.Ext ι ω := by
  classical
  let f : _root_.Formalism.CyclotomicNorms.Fbar g → ℂ := fun x => if h : x = 0 then 0 else ((ι (Units.mk0 x h) : ℂˣ) : ℂ)
  have hf0 : ∀ x (hx : x ≠ 0), f x = ((ι (Units.mk0 x hx) : ℂˣ) : ℂ) := fun x hx => dif_neg hx
  have hfz : f 0 = 0 := dif_pos rfl
  let ω : _root_.Formalism.CyclotomicNorms.Fbar g →*₀ ℂ :=
    { toFun := f
      map_zero' := hfz
      map_one' := by
        show f 1 = 1
        rw [hf0 1 one_ne_zero, Units.mk0_one, map_one, Units.val_one]
      map_mul' := by
        intro a b
        show f (a * b) = f a * f b
        by_cases ha : a = 0
        · rw [ha, zero_mul, hfz, zero_mul]
        by_cases hb : b = 0
        · rw [hb, mul_zero, hfz, mul_zero]
        rw [hf0 a ha, hf0 b hb, hf0 (a * b) (mul_ne_zero ha hb), Units.mk0_mul, map_mul,
          Units.val_mul] }
  refine ⟨ω, ?_, ?_⟩
  · intro a b hab
    change f a = f b at hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · exfalso
      rw [ha, hfz, hf0 b hb] at hab
      exact Units.ne_zero _ hab.symm
    · exfalso
      rw [hb, hfz, hf0 a ha] at hab
      exact Units.ne_zero _ hab
    · rw [hf0 a ha, hf0 b hb] at hab
      have := hι (Units.ext hab)
      simpa using congrArg Units.val this
  · intro u
    show _ = f u
    rw [hf0 u u.ne_zero, Units.mk0_val]

end GlobalTheory.GoodCharsCompare
