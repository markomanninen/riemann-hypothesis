module

public import Mathlib
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2

@[expose] public section

open NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.Count GlobalTheory.Dec

noncomputable section

namespace GlobalTheory.Published

def AutomorphicFormsFiniteUnitary : Prop := GlobalTheory.Dec.AutFinite

namespace AutFinU

end AutFinU

end GlobalTheory.Published

end
