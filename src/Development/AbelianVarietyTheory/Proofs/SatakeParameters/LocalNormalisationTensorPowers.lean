module

public import Mathlib
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormPow

@[expose] public section

namespace GlobalTheory

theorem locNormPow_tensorPowers : Formalism.L2.AlgTh.LocNormPow := Formalism.L2.AlgTh.local_norm_power

end GlobalTheory
