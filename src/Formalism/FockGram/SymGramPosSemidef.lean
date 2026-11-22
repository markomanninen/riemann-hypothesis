module

public import Formalism.FockGram.StatementFock
public import Formalism.FockGram.FockGramProofs.FockSesq
public import Formalism.FockGram.FockGramProofs.SubIndexNorm
public import Mathlib
public import Formalism.FockGram.FockGramProofs.CovolGram
public import Formalism.FockGram.FockGramProofs.HermDualOf
public import Formalism.FockGram.StatementLat
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Positive

@[expose] public section

namespace Formalism.E

theorem subIndexNorm : SubIndexNorm := indexEqNormDet

theorem hermDual : HermDual := hermDual_of subIndexNorm

end Formalism.E
