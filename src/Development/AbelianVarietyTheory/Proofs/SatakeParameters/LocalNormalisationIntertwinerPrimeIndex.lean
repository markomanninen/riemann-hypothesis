module

public import Mathlib
public import Formalism.LocalToGlobal.AlgebraicTheory.StatementNorm
public import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.NormInter

@[expose] public section

namespace GlobalTheory

theorem locNormInter : Formalism.L2.AlgTh.LocNormInter := Formalism.L2.AlgTh.local_norm_intertwiner

end GlobalTheory
