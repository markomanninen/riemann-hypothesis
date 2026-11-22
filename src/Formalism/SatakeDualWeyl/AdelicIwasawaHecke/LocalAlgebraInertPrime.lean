module

public import Formalism.SatakeDualWeyl.StatementG
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Transport
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit

@[expose] public section

noncomputable section

open Matrix TensorProduct NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section Gen

variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

end Gen

section Int

variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]

end Int

section Main

variable {A L : Type} [CommRing A] [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}

end Main

end Formalism.UG.P
