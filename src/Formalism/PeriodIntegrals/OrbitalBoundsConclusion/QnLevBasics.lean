module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian

@[expose] public section

theorem level_basics : Formalism.QuantumDeterminants.LevHom ∧ Formalism.QuantumDeterminants.LevUH ∧ Formalism.QuantumDeterminants.LevN ∧ Formalism.QuantumDeterminants.LevUW ∧ Formalism.QuantumDeterminants.LevWb ∧ Formalism.QuantumDeterminants.LevEll :=
  ⟨PI.QnLevBasicsW.level_group_homomorphism, PI.QnLevBasicsW.level_group_unitary_hermitian, PI.QnLevBasicsW.level_group_nilpotent,
    PI.QnLevBasicsW.level_group_unitary_weyl, PI.QnLevBasicsW.level_group_isotropic_vector, PI.QnLevBasicsW.level_group_ellipticity⟩
