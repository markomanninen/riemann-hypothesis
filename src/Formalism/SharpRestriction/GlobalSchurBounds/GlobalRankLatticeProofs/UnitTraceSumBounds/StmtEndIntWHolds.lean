module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.OkpInertOf
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtEndIntWOfOkp
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OkpInert
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.InertPrime

@[expose] public section

namespace Formalism.MainNotions.Ext

theorem okpInertG_holds : OkpInertG := integers_inert_prime

theorem inertPrime_holds : InertPrime := isPrime_span_of_jacobi_neg_one

theorem okpInert_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.GL3Theta.okpInert D := okpInert_of okpInertG_holds inertPrime_holds D

end Formalism.MainNotions.Ext
