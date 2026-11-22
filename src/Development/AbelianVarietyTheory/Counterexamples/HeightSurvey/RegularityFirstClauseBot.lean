module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree

@[expose] public section

noncomputable section

namespace GlobalTheory.TrivialValuationTest

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Ring

variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def powerSeriesCDVR (K : Type) [Field K] [CharZero K] : CDVR where
  V := PowerSeries K
  cpl := by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  ch0 := algebraRat.charZero _

end GlobalTheory.TrivialValuationTest
