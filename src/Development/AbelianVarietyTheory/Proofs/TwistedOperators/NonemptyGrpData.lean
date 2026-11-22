module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGrpDataMapHaar

@[expose] public section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible

namespace GlobalTheory.DetSqrtCover

theorem nonempty_grpData : ∀ p q : ℕ, Nonempty (GrpData p q) :=
  fun p q => ⟨grpOf p q MeasureTheory.Measure.haar⟩

end GlobalTheory.DetSqrtCover
