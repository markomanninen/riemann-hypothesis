module

public import Formalism.CMTypeGalois.CMTypeFrobenius.MQGalois
public import Formalism.CMTypeGalois.CMTypeFrobenius.MQKummer
public import Formalism.CMTypeGalois.StatementField
public import Mathlib
public import Formalism.StatementCM

@[expose] public section

open NumberField Ideal

namespace Formalism.Q3

theorem mqKummer : MQKummer := mqKummer_of mqGalois

end Formalism.Q3
