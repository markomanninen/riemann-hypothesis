module

public import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTEx
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePOAct
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePAllStart
public import Formalism.LocalToGlobal.CharacterGerms.EndomorphismLimitIntegral
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallMain
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelfEx
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePOActSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStabSelf

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

theorem ptSelf_of_start2 (hS : AllStartSelfSt) : PTSelfSt :=
  ptSelf_of_start hS OActSelf.oActSelf_holds hStabSelf_holds

end Formalism.L2.FormalSeriesBounds
