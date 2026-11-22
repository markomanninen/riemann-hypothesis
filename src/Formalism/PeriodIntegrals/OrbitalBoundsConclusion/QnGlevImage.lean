module

public import Mathlib
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelImageArithmetic.GlevImageOf

@[expose] public section

theorem gl_level_image : Formalism.QuantumDeterminants.LevHom → Formalism.QuantumDeterminants.LevUH → Formalism.FourierDecayAlt.Q.GlevImage :=
  QnGlevImageW.glevImage_of
