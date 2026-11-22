module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.EqZeroOfNegMap

@[expose] public section

open Matrix Formalism.QuantumDeterminants

noncomputable section
namespace PI.FrameInd

theorem negative_bound : NegBound := fun k r S hS => NegB.negBound k r S hS

end PI.FrameInd
