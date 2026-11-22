module

public import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSLowK
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSFdeg
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.DSRatio

@[expose] public section

namespace Formalism.QuantumDeterminants

theorem fdegPos : FdegPos := formal_degree_pos_holds
theorem fdegRatio : FdegRatio := formalDegreeShiftRatio_holds
theorem capelliHW : CapelliHW := capelliHighestWeight_holds

end Formalism.QuantumDeterminants
