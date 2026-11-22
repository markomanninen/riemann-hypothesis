module

public import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTEig
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEig2

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_holds : PTSelfSt := ptSelf_of_eig RowTiePKey.keyEig_holds

end Formalism.L2.FormalSeriesBounds
