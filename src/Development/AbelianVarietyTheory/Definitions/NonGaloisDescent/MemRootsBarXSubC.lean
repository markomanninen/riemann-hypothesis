module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

@[expose] public section

noncomputable section
namespace GlobalTheory.GLq.Model
open Polynomial Formalism.CyclotomicNorms

variable (g : ℕ) [hg : Fact g.Prime]

theorem N_pos {d : ℕ} (hd : 0 < d) : 0 < g ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hg.out.one_lt)


open Formalism.MainNotions.ArithmeticCylinders
variable {g}

theorem thetaOf_gen_pow (L : LabelDatum g) {d : ℕ} (hd : 0 < d) {x : Fbar g} (hx : x ^ (g ^ d - 1) = 1) (n : ℕ) :
    thetaOf L d x (L.gen d ^ n) = L.teich x ^ n := by
  have hex : ∃ m : ℕ, L.gen d ^ n = L.gen d ^ m := ⟨n, rfl⟩
  rw [thetaOf, dite_eq_left hex]
  have hm := hex.choose_spec
  have hN := N_pos g hd
  have hP : IsPrimitiveRoot (L.gen d) (g ^ d - 1) :=
    L.gen_order d hd ▸ IsPrimitiveRoot.orderOf (L.gen d)

  have h1 : n % (g ^ d - 1) = hex.choose % (g ^ d - 1) := by
    apply hP.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN)
    rw [← L.gen_order d hd, pow_mod_orderOf, pow_mod_orderOf]
    exact hm
  have h2 : orderOf (L.teich x) ∣ g ^ d - 1 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have h3 : n % orderOf (L.teich x) = hex.choose % orderOf (L.teich x) := Nat.ModEq.of_dvd h2 h1
  calc L.teich x ^ hex.choose = L.teich x ^ (hex.choose % orderOf (L.teich x)) :=
        (pow_mod_orderOf _ _).symm
    _ = L.teich x ^ (n % orderOf (L.teich x)) := by rw [h3]
    _ = L.teich x ^ n := pow_mod_orderOf _ _

theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  rw [toG, dite_eq_left x.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem tl_self {n : ℕ} (M : Mt g n) : tl n M = M := by
  ext i j
  simp [tl, entN]

theorem hc_full {n : ℕ} (α : Gn g n → ℂ) (hα : IsClass α) : hc n 0 α (fun _ => 1) n = α := by
  funext x

  have hpar : ∀ M : Mt g n, InPar n M := fun M i j _ hi => absurd i.isLt (not_lt.mpr hi)
  have hα' : ∀ y : Gn g n, α (y⁻¹ * x * y) = α x := fun y => by
    simpa using hα x y⁻¹
  have hcard : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [hc, hcT, hpar, if_true, mul_one, tl_self, toG_coe, hα', Finset.sum_const,
    Finset.filter_true, Finset.card_univ, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ hcard _

end GlobalTheory.GLq.Model
