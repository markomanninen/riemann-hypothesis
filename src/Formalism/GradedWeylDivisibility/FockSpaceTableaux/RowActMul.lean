module

public import Formalism.GradedWeylDivisibility.StatementD

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem row_action_mul : RowActMul := by
  intro R _ k n g h
  apply MvPolynomial.algHom_ext
  intro v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, rowAct, aeval_X, map_sum, map_mul, aeval_C, Matrix.mul_apply,
    MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end Formalism.GradedWeylDivisibility
