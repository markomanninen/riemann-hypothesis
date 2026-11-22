module

public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.WeierstrassSubstitution.DivisionLogarithm

@[expose] public section

universe u v

namespace Formalism.L2.Th1.A

theorem divSpec : DivSpec.{u, v} := division_spec

end Formalism.L2.Th1.A
