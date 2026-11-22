module

public import Mathlib
public import Formalism.PeriodIntegrals.OddDualWeyl
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.OddDualWeylFactorization

@[expose] public section

theorem oddDualWeyl {K : Type} [Field K] (O : Type) [CommRing O] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    PI.OddDualWeyl.OddFact (K := K) O m lam :=
  PI.OddDualWeyl.odd_dual_weyl_factorization O m lam
