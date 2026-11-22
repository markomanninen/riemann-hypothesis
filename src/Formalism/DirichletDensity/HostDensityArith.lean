module

public import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
public import Formalism.DirichletDensity.DirichletDensityProofs.MQDiscr
public import Formalism.DirichletDensity.DirichletDensityProofs.APLogDensity
public import Mathlib
public import Formalism.DirichletDensity.Statement
public import Formalism.CMTypeGalois.HalfTypesFromGeneral

@[expose] public section

namespace Formalism.HF.Final

theorem quadDiscr : Formalism.HF.QuadDiscr := Formalism.HF.quadDiscr
theorem mqDiscr : Formalism.HF.MQDiscr := Formalism.HF.mqDiscr_of quadDiscr

end Formalism.HF.Final
