module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieCartTop
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

theorem germIAll_holds : GermIAllSt := fun _ _ _ _ _ _ _ _ Y => germI_holds Y

end Formalism.L2.FormalSeriesBounds
