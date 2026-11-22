module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
public import Formalism.ZetaNonvanishing.ZetaLandau

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.ZetaZeroFreeRegion

theorem G_eq_Gz (y : ℝ) : Formalism.MainNotions.GlobalTheoryTheory.G y = Formalism.Gz y := by
  rw [Formalism.MainNotions.GlobalTheoryTheory.G_eq_Gfun]
  unfold Formalism.BasicNotions.Gfun Formalism.Gz Formalism.Sz
  ring

end Formalism.MainNotions.ZetaZeroFreeRegion

end
