module

public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEigD
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyTeich2
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyJoint

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

theorem keyEig_holds : KeyEigSt := RowTiePKeyEig.keyEig_of RowTiePKeyTeich.teich_holds jointEig_holds

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
