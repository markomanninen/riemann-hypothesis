module

public import Mathlib

@[expose] public section

namespace GlobalTheory.SquareZeroLeibnizPoint

open TrivSqZeroExt

section PointsOfDual

variable {O C : Type*} [CommRing O] [CommRing C] {ι : Type*} [Fintype ι]

end PointsOfDual

section Leibniz

variable {A O M : Type*} [CommRing A] [CommRing O] [AddCommGroup M] [Module O M]

theorem leibniz_map_one (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) : d 1 = 0 := by
  have h := hd 1 1
  simpa using h

variable [Module Oᵐᵒᵖ M] [IsCentralScalar O M]

def sqzOfLeibniz (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) : A →+* TrivSqZeroExt O M where
  toFun f := (ε f, d f)
  map_one' := TrivSqZeroExt.ext (map_one ε) (leibniz_map_one ε d hd)
  map_zero' := TrivSqZeroExt.ext (map_zero ε) (map_zero d)
  map_add' f f' := TrivSqZeroExt.ext (map_add ε f f') (map_add d f f')
  map_mul' f f' := TrivSqZeroExt.ext (map_mul ε f f') (by
    change d (f * f') = ε f • d f' + MulOpposite.op (ε f') • d f
    rw [op_smul_eq_smul]
    exact hd f f')

end Leibniz

end GlobalTheory.SquareZeroLeibnizPoint
