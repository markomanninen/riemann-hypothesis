module

public import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

@[expose] public section

namespace Formalism.FourierDecayAlt.P.S3x2

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3

section Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] {A : Type} [CommRing A]

variable {c : ι → ℕ} {x y : Matrix ι ι A}


end Generic

section Prod

variable {G : Type} [Group G]

end Prod

section Specific

variable {A : Type} [CommRing A] {r k : ℕ}




end Specific

section Local

variable (o : Type) [CommRing o] [IsLocalRing o]

variable {o} {r k : ℕ}

end Local

end Formalism.FourierDecayAlt.P.S3x2

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3 Formalism.FourierDecayAlt.P.S3x2

end Formalism.FourierDecayAlt.P
