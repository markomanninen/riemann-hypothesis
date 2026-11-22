module

public import Mathlib
public import Formalism.PeriodIntegrals.LatMin
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinimalLatticeNorm.NormTwoEqOne

@[expose] public section

namespace PI

theorem exists_minimalNormVector : PI.LatMin := by
  intro p _ σ B L W hp2 _ _ hL hsm hadd hsym hne
  refine PI.LatMinWork.main hp2 B L hL ?_ hadd hsym hne
  intro c u v
  have h : c • u = (c : ℚ_[p]) • u := (algebraMap_smul ℚ_[p] c u).symm
  rw [h, hsm]

end PI
