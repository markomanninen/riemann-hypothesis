module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwSandwichOf
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwGaussUniq
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwPhiForm
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwBigCellG
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SwPhiDeriv
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLIso
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHDim

@[expose] public section

namespace Formalism.L2.SG.Pf.BH

theorem sandwich' : Sandwich := by
  refine sandwich_of_chart Sw.lieG' Sw.lieWb' gauss_sum_unique phi_form' big_cell_g
    (phiDeriv_of Sw.w0Sq) Sw.lIso Sw.w0Sq ?_ ?_
  · unfold PI.SwSand.LieEN
    intros
    exact Formalism.MainNotions.BridgeCSB.lieE_N
  · intros
    apply Formalism.MainNotions.BridgeCSB.exp_mem_N

end Formalism.L2.SG.Pf.BH
