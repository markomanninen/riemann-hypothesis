module

public import Mathlib
public import Formalism.FrobeniusContraction.HighestWeightResidueAvoids
public import Formalism.WindowSums.PowerSeriesRelationList
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij
public import Formalism.FrobeniusContraction.Statement
public import Formalism.FrobeniusContraction.StatementTop

@[expose] public section

namespace Formalism.ZetaNonvanishing.ARCV

open Polynomial

theorem range_sdiff_range (H : ℕ) : Finset.range (2 * H) \ Finset.range H = Finset.Ico H (2 * H) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
  omega

end Formalism.ZetaNonvanishing.ARCV
