module

public import Formalism.SatakeDualWeyl.StatementC
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SatakeDualWeyl.StatementF

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain TensorProduct

namespace Formalism.UG

def IsInertAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal

end Formalism.UG
