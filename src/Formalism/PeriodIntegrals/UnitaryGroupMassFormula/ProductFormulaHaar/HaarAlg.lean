module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarScale
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarTransv

@[expose] public section

namespace PI.ProdFormulaE.HaarAlgP

theorem haarScaling : St.HaarAlg := by
  refine haarAlg_of ?_ ?_
  · intro K _ _ _ _ E _ _ _ _ _ _ n b μ _ i a ha
    exact PI.ProdFormulaE.HaarBox.scale_box b μ i a ha
  · intro K _ _ _ _ E _ _ _ _ n b t
    exact PI.ProdFormulaE.HaarBox.transvection_box b t

end PI.ProdFormulaE.HaarAlgP
