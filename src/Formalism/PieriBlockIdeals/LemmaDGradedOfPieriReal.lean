module

public import Mathlib
public import Formalism.PieriBlockIdeals.StatementLC
public import Formalism.PieriBlockIdeals.StatementLP
public import Formalism.PieriBlockIdeals.StatementLR

@[expose] public section

namespace Formalism.CohomologicalDescent.ColumnMinorsFromPieri

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

def ColumnsRealOfPieriReal : Prop := LR.PieriReal → LR.ColumnsReal

end Formalism.CohomologicalDescent.ColumnMinorsFromPieri
