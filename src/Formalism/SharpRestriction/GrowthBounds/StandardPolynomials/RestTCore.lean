module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCGlue
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestSegCoreOfNum
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCXNum

@[expose] public section

namespace Formalism.MainNotions.ColumnSystems.Pf

theorem restTCore : RestTCore := restTCore_of_seg (restSegCore_of_num restNumCore)

end Formalism.MainNotions.ColumnSystems.Pf
