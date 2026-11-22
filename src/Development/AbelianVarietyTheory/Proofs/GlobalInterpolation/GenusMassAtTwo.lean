module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll

@[expose] public section

namespace GlobalTheory

theorem genusMassAt_two : ∀ D : Formalism.BasicNotions.D7, Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.GenusMassAt D 2 :=
  fun D => Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.genusMassAt_of D (genusMassStd_all D) 2

end GlobalTheory
