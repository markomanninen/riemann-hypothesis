module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.LIdemLiftPf
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsMonicFactorLiftOfPowMulSubOnePow

@[expose] public section

noncomputable section

theorem UpperTheory.liftIdempotentFactorization_holds :
    LateralTheory.E.LIdemLiftPf.LFact := by
  intro A _ I _ g hg n m h
  exact UpperTheory.exists_monic_factor_lift_of_pow_mul_sub_one_pow A I g hg n m h

end
