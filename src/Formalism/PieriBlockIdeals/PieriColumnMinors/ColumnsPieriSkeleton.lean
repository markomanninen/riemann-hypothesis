module

public import Formalism.PieriBlockIdeals.LemmaDGradedOfPieriReal
public import Formalism.PieriBlockIdeals.PieriColumnMinors.LemmaDSkeletonFour
public import Formalism.PieriBlockIdeals.PieriColumnMinors.PieriGenerated

@[expose] public section

namespace Formalism.CohomologicalDescent.ColumnMinorsFromPieri

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem columns_real_of_pieri_real : ColumnsRealOfPieriReal := by
  intro hP p q w lam2 hanti hle n tau hcol z hz
  exact Formalism.CohomologicalDescent.LC.columns_from_pieri ℚ (Fin p) _ q _ n lam2 (hP p q w lam2 hanti hle n) tau
    (by simpa using hcol) z hz

end Formalism.CohomologicalDescent.ColumnMinorsFromPieri
