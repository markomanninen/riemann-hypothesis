module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSBoxVolPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSOmDecomp
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSAdTup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSKfOrb
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSLocSB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSWittLoc

@[expose] public section

noncomputable section

namespace Formalism.L2.SG.Pf.NcS.SplitPf

open Formalism.L2.SG.Pf.NcS

theorem omega_finite_volume_of_witt (hW : LocSBPf.WittLocT) (hI : LocSBPf.IntWittAE) : SplitSk.OmFinVol := by

  have hLoc : FinVolSk.LocSB := LocSBPf.locSB_of hW hI
  exact FinVolSk.omFinVol_of KfOrbPf.finite_orbit_holds hLoc BoxVolPf.box_volume_holds

theorem omega_splitting_of_witt (hW : LocSBPf.WittLocT) (hI : LocSBPf.IntWittAE) : Formalism.L2.SG.Pf.NcSplitS.SplitOm := by

  apply SplitSk.splitOm_of AdTupPf.admissible_tuple_holds OmDecompPf.omega_decomposition_holds
  exact omega_finite_volume_of_witt hW hI

theorem splitOm_of_intWitt (hI : LocSBPf.IntWittAE) : Formalism.L2.SG.Pf.NcSplitS.SplitOm := by

  exact omega_splitting_of_witt WittLocPf.local_witt_theorem hI

end Formalism.L2.SG.Pf.NcS.SplitPf
