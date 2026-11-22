module

public import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Formalism.FourierDecayAlt.P.S3x8

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3

section Key

variable {A F : Type} [CommRing A] [CommRing F]

end Key

section Corner

variable {A F : Type} [CommRing A] [CommRing F]

end Corner

section Maps

variable {A F : Type} [CommRing A] [CommRing F]

end Maps

section DVR

variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0]

variable [IsDomain o] [IsDiscreteValuationRing o]

end DVR

section Blocks

variable {A : Type} {r k : ℕ}

variable [CommRing A]

section mk
variable (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A)
end mk

end Blocks

section Stab

variable {F : Type} [Field F] {r k : ℕ}

end Stab

section Forcing

variable {o : Type} [CommRing o] {k0 : Type} [Field k0] [Algebra o k0] {r k : ℕ}

variable [IsDomain o] [IsDiscreteValuationRing o] [IsFractionRing o k0]


end Forcing

end Formalism.FourierDecayAlt.P.S3x8
