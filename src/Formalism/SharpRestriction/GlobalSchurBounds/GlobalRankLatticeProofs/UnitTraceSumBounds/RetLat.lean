module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.SigmaStarUniq
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AreaLat
public import Mathlib
public import Formalism.PeriodIntegrals.LatDefs
public import Formalism.PeriodIntegrals.AreaLat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarUniq
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DiscrNe
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SigmaStarEx

@[expose] public section

namespace Formalism.MainNotions.Ext

theorem discrNe_holds : DiscrNe := discrNe'

theorem sigmaStarEx_holds : SigmaStarEx := sigma_star_exists

end Formalism.MainNotions.Ext
