module

public import Mathlib
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ

@[expose] public section

noncomputable section

open MeasureTheory

namespace PI.UJUnimod

def UJRightInv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), (Formalism.REAL.muG ε).IsMulRightInvariant

end PI.UJUnimod
