module

public import Mathlib
public import Formalism.HermitianLattices.StatementMass
public import Formalism.LogVandermondeBounds.LogRatioLowerBound
public import Formalism.LogVandermondeBounds.LogRatioUpperBound

@[expose] public section

open NumberField Finset

namespace Formalism.HermitianLattices.SiegelMassBounds

def SiegelMassRatioThm : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio

end Formalism.HermitianLattices.SiegelMassBounds
