module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneSevenOfFiniteOrder
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.CMFieldLemmas
public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.BranchingInterlacingPairs
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FinOrdAd

@[expose] public section

namespace Formalism.MainNotions.Ext

theorem finOrdG_holds : FinOrdG := finite_order_adelic

end Formalism.MainNotions.Ext

namespace Formalism.MainNotions.UnusedSlot33

theorem division_rational_lattice (D : Formalism.BasicNotions.D7) : division_rows_rational_lattice D :=
  finiteModel_of_heckeEstimate D (finite_order_of_totally_real Formalism.MainNotions.Ext.finOrdG_holds D)

end Formalism.MainNotions.UnusedSlot33
