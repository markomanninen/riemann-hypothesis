module

public import Mathlib

@[expose] public section

universe u_1 u_3

namespace UpperTheory.Reformulated.B.ThetaInvolution

noncomputable def Jmat (R : Type u_1) [CommRing R] (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i j ↦ if j = i.rev then (1 : R) else (0 : R)

theorem aux2 {R : Type u_1} [CommRing R] (m : ℕ) :
    Jmat R m * Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp only [Jmat, Matrix.one_apply, if_true, one_mul, Fin.rev_rev]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (fun e => h e.symm), if_neg h]
  · intro k _ hk
    simp [Jmat, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

noncomputable def Jgl (R : Type u_1) [CommRing R] (m : ℕ) : GL (Fin m) R :=
  { val := Jmat R m, inv := Jmat R m, val_inv := aux2 m, inv_val := aux2 m :
    (Matrix (Fin m) (Fin m) R)ˣ }

theorem aux4 {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) :
    (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]

theorem aux5 {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) :
    (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]

noncomputable def trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g : GL n R) : GL n R :=
  { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose,
    val_inv := aux4 g, inv_val := aux5 g : (Matrix n n R)ˣ }

noncomputable def theta {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) : GL (Fin m) R :=
  Jgl R m * trInv g * Jgl R m

private theorem Jgl_mul_self (R : Type u_1) [CommRing R] (m : ℕ) : Jgl R m * Jgl R m = 1 :=
  Units.ext (aux2 m)

private theorem trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g h : GL n R) : trInv (g * h) = trInv g * trInv h := by
  apply Units.ext
  change (((g * h)⁻¹ : GL n R) : Matrix n n R).transpose =
    ((g⁻¹ : GL n R) : Matrix n n R).transpose * ((h⁻¹ : GL n R) : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g : GL n R) : trInv (trInv g) = g := by
  apply Units.ext
  change (g : Matrix n n R).transpose.transpose = (g : Matrix n n R)
  exact Matrix.transpose_transpose _

private theorem trInv_Jgl (R : Type u_1) [CommRing R] (m : ℕ) : trInv (Jgl R m) = Jgl R m := by
  apply Units.ext
  change (Jmat R m).transpose = Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, Jmat]
  by_cases h : j = i.rev
  · rw [if_pos h, if_pos (by rw [h, Fin.rev_rev])]
  · rw [if_neg h, if_neg (fun e => h (by rw [e, Fin.rev_rev]))]

theorem aux8 {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) : theta (theta g) = g := by
  have hJ := Jgl_mul_self R m
  simp only [theta, trInv_mul, trInv_trInv, trInv_Jgl]
  calc _ = (Jgl R m * Jgl R m) * g * (Jgl R m * Jgl R m) := by simp only [mul_assoc]
    _ = g := by rw [hJ, one_mul, mul_one]

theorem aux9 {m : ℕ} {R : Type u_1} [CommRing R] (g h : GL (Fin m) R) :
    theta (g * h) = theta g * theta h := by
  have hJ := Jgl_mul_self R m
  simp only [theta, trInv_mul]
  calc _ = Jgl R m * trInv g * 1 * trInv h * Jgl R m := by rw [mul_one]; simp only [mul_assoc]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def thetaAut (m : ℕ) (R : Type u_1) [CommRing R] : MulAut (GL (Fin m) R) :=
  { toFun := theta, invFun := theta, left_inv := aux8, right_inv := aux8, map_mul' := aux9 :
    GL (Fin m) R ≃* GL (Fin m) R }

theorem aux11 (m : ℕ) (R : Type u_1) [CommRing R] :
    (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) =
      (1 : MulAut (GL (Fin m) R)) :=
  if_pos rfl

private theorem thetaAut_mul_self (m : ℕ) (R : Type u_1) [CommRing R] :
    thetaAut m R * thetaAut m R = 1 :=
  MulEquiv.ext (fun g => aux8 g)

theorem aux12 (m : ℕ) (R : Type u_1) [CommRing R] (s t : ℤˣ) :
    (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) =
      (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) *
        if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R := by
  have hn : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp [hn]
  · simp [hn]
  · simp [hn, thetaAut_mul_self]

noncomputable def sgnAct (m : ℕ) (R : Type u_1) [CommRing R] : ℤˣ →* MulAut (GL (Fin m) R) :=
  { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else thetaAut m R,
    map_one' := aux11 m R, map_mul' := aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def GG (m : ℕ) (R : Type u_1) [CommRing R] : Type u_1 :=
  GL (Fin m) R ⋊[sgnAct m R] ℤˣ

@[reducible] noncomputable def ofGL {m : ℕ} {R : Type u_1} [CommRing R] : GL (Fin m) R →* GG m R :=
  SemidirectProduct.inl

noncomputable def conjBy {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G]
    (h : GL (Fin m) R) (r : G →* GG m R) : G →* GG m R :=
  (MulAut.conj (ofGL h : GG m R)).toMonoidHom.comp r

theorem conjBy_conjBy {C D : Type} [CommRing C] [Group D] (h h' : GL (Fin (3 : ℕ)) C)
    (r : D →* GG (3 : ℕ) C) : conjBy (h * h')⁻¹ (conjBy h r) = conjBy h'⁻¹ r := by
  ext1 x
  have e1 : (ofGL (h * h')⁻¹ : GG 3 C) = (ofGL h * ofGL h')⁻¹ := by rw [map_inv, map_mul]
  have e2 : (ofGL h'⁻¹ : GG 3 C) = (ofGL h')⁻¹ := map_inv _ _
  change MulAut.conj (ofGL (h * h')⁻¹) (MulAut.conj (ofGL h) (r x)) = MulAut.conj (ofGL h'⁻¹) (r x)
  rw [e1, e2]
  generalize (ofGL h : GG 3 C) = a
  generalize (ofGL h' : GG 3 C) = b
  generalize r x = y
  simp only [MulAut.conj_apply]
  group

end UpperTheory.Reformulated.B.ThetaInvolution
