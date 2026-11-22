module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Assembly
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.AreaCmLNe
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.NormIntKur

@[expose] public section

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame

theorem hermFrame_of_locCore (hL : LocCore) : Formalism.L2.Th1.Top.FrP.HermFrame := hermFrame_of frobStep ratStep hL

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
