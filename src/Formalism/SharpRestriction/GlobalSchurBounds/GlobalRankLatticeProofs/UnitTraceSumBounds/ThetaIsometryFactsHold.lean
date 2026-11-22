module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MonomialFrameSpan.DetSubmatrixFun
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IsometryDerivative.ExistsOePerm
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwCauchyBinet
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwMain
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwInjective

@[expose] public section

namespace Formalism.MainNotions.GL3Columns

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

theorem wwCB_holds (D : D7) : wwCB D := fun k _ N nu y => cauchy_binet_minors (Bool × HH D) k N nu y

theorem ww_holds (D : D7) : ww D :=
  fun l _ N0 N1 nu Th ph Q hQ y' => minor_identity (Bool × HH D) l N0 N1 nu Th ph Q hQ y'

theorem wwInj_holds (D : D7) : wwInj D :=
  fun l _ N nu ph hy J => wwInjective_of cauchy_binet_minors (Bool × HH D) l N nu ph hy J

end Formalism.MainNotions.GL3Columns
