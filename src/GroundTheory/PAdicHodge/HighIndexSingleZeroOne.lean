module

public import Mathlib
public import GroundTheory.PAdicHodge.RobbaSeries

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

structure AnnulusRing (I : Set ℝ) where

@[ext]
structure Robba where

  coeff : ℤ → K
  exists_convergesAt' : ∃ r < 1, ∀ ρ, r ≤ ρ → ρ < 1 → 0 < ρ → ConvergesAt coeff ρ

variable {K}

namespace AnnulusRing

variable {I : Set ℝ}

variable [hI : Fact (∃ ρ ∈ I, 0 < ρ)]

end AnnulusRing

namespace Robba

end Robba

namespace AnnulusRing

variable {r : ℝ} [Fact (r < 1)]

end AnnulusRing

namespace Robba

end Robba

namespace Laurent

end Laurent

namespace Robba

end Robba

namespace Laurent

end Laurent

namespace Robba

end Robba

end GroundTheory.PAdicHodge
