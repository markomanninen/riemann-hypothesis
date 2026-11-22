module

public import Formalism.MahlerMeasure.MahlerMeasureProofs.DeterminantBlockLeadingTerm
public import Formalism.MahlerMeasure.Statement
public import Formalism.MahlerMeasure.MahlerMeasureProofs.Mahler
public import Mathlib

@[expose] public section

namespace Formalism.GM.Top
open Formalism.GM
theorem detBlockLead : DetBlockLead := determinant_block_leading_term
end Formalism.GM.Top
