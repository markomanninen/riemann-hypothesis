module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic

@[expose] public section

namespace Formalism.BasicNotions

abbrev minkM (n : ℕ) : ℕ := Formalism.HermitianLatticeCounting.S6.minkowskiM n

def DGamMink (D : D7) : Prop := (D.mem D.u₀).C.DGam = minkM (2 * D.R.f * D.R.N D.R.m)

end Formalism.BasicNotions
