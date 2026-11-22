module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MExistsCut
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MeasWCore
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MeasInfXfer

@[expose] public section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.St

theorem mExists_holds : ∀ D : D7, MExists D :=
  fun D => Formalism.L2.SG.Pf.mExists_of_cuts D weil_measure_compat infinite_measure_transfer

end GlobalTheory.St
