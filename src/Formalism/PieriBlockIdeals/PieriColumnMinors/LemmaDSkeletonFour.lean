module

public import Formalism.PieriBlockIdeals.StatementLC
public import Formalism.PieriBlockIdeals.PieriColumnMinors.PathEqOfContentSequence
public import Formalism.PieriBlockIdeals.PieriColumnMinors.AntitoneShapes
public import Formalism.PieriBlockIdeals.PieriColumnMinors.PermutationWeightInvariant
public import Formalism.PieriBlockIdeals.PieriColumnMinors.MeasureSwapInvariant

@[expose] public section

namespace Formalism.CohomologicalDescent.LC

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem antitone_increment : AntiStep := AntiStep_of no_bad_tuple

theorem columns_from_pieri : ColumnsFromPieri :=
  ColumnsFromPieri_of swap_path_exists same_column measure_swap_invariant monotone_run weight_iff_condition good_swap_exists
    antitone_increment antitone_shapes

end Formalism.CohomologicalDescent.LC
