module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import CompanionTheory.AutomorphicTheory.UniformLocalFormulas.Closed
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StepChoiceConstantsCOfSiegelWeilAtInfinity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowPositivityOfSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneOnSingletonOfSiegelWeil

@[expose] public section

namespace GlobalTheory.Core.Diag

theorem oneOn_singleton_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent →
      ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true ∧ GlobalTheory.Core.Diag.OneOn {c} false :=
  fun h => oneOn_singleton_of_siegelWeil_of_stepChoice h
    (GlobalTheory.St.stepChoiceDataC_of_siegelWeil_inInfinity h (fun _ X u u' hg =>
      Formalism.L2.SG.RealObj.EnergyConvJ.BM.realObj_inInfinityX_jsz
        CompanionTheory.Lime.BM.uniqGap_holds hg X u u' 1 one_pos))
    Formalism.MainStatements.RowRest.bDat_theoremB_global (GlobalTheory.rowNGP_of_siegelWeil h)

end GlobalTheory.Core.Diag
