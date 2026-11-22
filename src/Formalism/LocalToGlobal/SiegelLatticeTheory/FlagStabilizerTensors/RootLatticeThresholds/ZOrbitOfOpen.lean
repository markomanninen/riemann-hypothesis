module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZSt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZZLoc
public import Formalism.SelfDualUnimodular.LocalLatticeDictionary.SemiGenusLocal
public import Formalism.SelfDualUnimodular.LocalLatticeDictionary.AlgebraMapNeZero
public import Formalism.SelfDualUnimodular.LocalLatticeDictionary.LocFin

@[expose] public section

namespace Formalism.L2.SG.Pf.LatDictZ

theorem zOrbit_of_open (hP : Z0.PrimPlaneLoc) (hA : Z0.AdelGlue) : LatDictZ.ZOrbit :=
  Z0.zOrbit_of (Z0.BR.semiGenusZ_of (Z3.semiGenusZLoc_of Z0.SGC.semi_genus_local hP)) hA
    Z0.LF.lattice_locally_finite

end Formalism.L2.SG.Pf.LatDictZ
