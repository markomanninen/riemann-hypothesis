module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransferOfFacts
public import Formalism.LocalToGlobal.IndefiniteReal.TraceOfDiag
public import Formalism.LocalToGlobal.IndefiniteReal.OpNormAtLeOfPoints
public import Formalism.LocalToGlobal.IndefiniteReal.FinrankIntSelf
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsStrictHenselianAbsolutelyClosedLocalRing

@[expose] public section

namespace Formalism.IndefR.LatticeTransfer

theorem dimSq : DimSq := dimSq_of schur

theorem idemP : IdemP := idemP_of charFacts

theorem core : Core := core_of charFacts keyZero schur idemP

theorem all_parts_transfer_holds : AllPartsTransfer := all_parts_transfer_of_facts idemE idemP core dimSq metric

end Formalism.IndefR.LatticeTransfer
