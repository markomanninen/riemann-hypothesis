module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.IsUnitaryK
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.HermFrameOfLocCore
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.LocMain
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.AreaCmLNe

@[expose] public section

namespace Formalism.L2.Th1.Top.FrP

theorem hermFrame_holds : HermFrame :=
  UnitaryGroupMassFormula.HermFrame.hermFrame_of_locCore UnitaryGroupMassFormula.HermFrame.Loc.local_core'

end Formalism.L2.Th1.Top.FrP
