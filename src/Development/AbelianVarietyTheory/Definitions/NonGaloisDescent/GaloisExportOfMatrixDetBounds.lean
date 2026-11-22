module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen
open scoped ENNReal TensorProduct

namespace GlobalTheory.TwSys.Test

section Ord
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

end Ord

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}



end GlobalTheory.TwSys.Test

end
