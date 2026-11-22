module

public import Formalism.PeriodIntegrals.InHHClassFin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.ClassSetFinIdx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.OneMemKg
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.SigConj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.HformSumRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.FrHformSumLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.CTFromBlocks
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.RtUnitaryOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianClassFiniteness.LevelStep

@[expose] public section

theorem stabClassFinite : PI.InHHClassFin.StabClassFinite :=
  PI.UnitaryGroupMassFormula.InHHClassFin.stabClassFinite_of_steps
    (fun _ _ Γ K K' h => PI.UnitaryGroupMassFormula.InHHClassFin.classSet_mono Γ K K' h)
    (fun _ _ Γ K K' h hi => PI.UnitaryGroupMassFormula.InHHClassFin.classSet_finIdx Γ K K' h hi)
    (fun _ _ _ _ Φ Γ K => PI.UnitaryGroupMassFormula.InHHClassFin.classSet_map Φ Γ K)
    PI.UnitaryGroupMassFormula.InHHClassFin.kgNhd PI.UnitaryGroupMassFormula.InHHClassFin.sigConj PI.UnitaryGroupMassFormula.InHHClassFin.frameExists
    PI.UnitaryGroupMassFormula.InHHClassFin.frameIso PI.UnitaryGroupMassFormula.InHHClassFin.frameGram PI.UnitaryGroupMassFormula.InHHClassFin.frameRat
    PI.UnitaryGroupMassFormula.InHHClassFin.levelStep
