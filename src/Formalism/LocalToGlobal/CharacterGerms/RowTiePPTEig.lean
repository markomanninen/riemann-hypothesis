module

public import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTClose
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLieSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyGlue
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDelta
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePSplitLA
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyRes2

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_of_eig (hE : RowTiePKey.KeyEigSt) : PTSelfSt :=
  ptSelf_of_start2 (allStartSelf_of_eig hE)

end Formalism.L2.FormalSeriesBounds
