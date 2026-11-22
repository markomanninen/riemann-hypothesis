module

public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

namespace Formalism.UG.P

open Matrix MvPolynomial

theorem linSubst_comp (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]
    (M N : Matrix n n O) :
    (Formalism.UG.linSubst O n M).comp (Formalism.UG.linSubst O n N) = Formalism.UG.linSubst O n (N * M) := by
  apply MvPolynomial.algHom_ext
  intro i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.linSubst, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

theorem linSubst_one (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n] :
    Formalism.UG.linSubst O n 1 = AlgHom.id O _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [Formalism.UG.linSubst, Matrix.one_apply]

theorem polynomial_action_mul_holds : Formalism.UG.PolyActMul := by
  intro O _ n _ _ g h
  refine ⟨?_, ?_⟩
  · unfold Formalism.UG.polyAct
    rw [linSubst_comp, _root_.mul_inv_rev, Units.val_mul]
  · unfold Formalism.UG.polyAct
    rw [inv_one, Units.val_one, linSubst_one]

end Formalism.UG.P
