module

public import Formalism.LocalToGlobal.UnitaryNorms.CharExCol
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AlgValsFin

@[expose] public section

namespace Formalism.L2.Host

namespace CharEx

theorem algValsFin (L : Type) [Field L] [NumberField L] : AlgValsFin L := algebraic_values_finite L

end CharEx

end Formalism.L2.Host
