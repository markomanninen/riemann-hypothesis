module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.T2SpaceFiniteAdelesExt
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.AdeleIntA

@[expose] public section

noncomputable section

namespace PI.IwaMeasEx.Nrm

open NumberField IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open Formalism.MainNotions.S

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


end Gen

section Unit

open Formalism.L2.S.S7.GLOne

variable (I : AutInst)

abbrev iE : I.E →+* AEf I := Formalism.UG.inclE (F := I.F) (Af I.F)

end Unit

end PI.IwaMeasEx.Nrm

end
