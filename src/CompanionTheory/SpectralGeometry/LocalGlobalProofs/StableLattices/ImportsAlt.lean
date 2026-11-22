module

public import Mathlib
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperator
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports

@[expose] public section

namespace GlobalTheory.CompanionTheory.DSCapelliAction

theorem actQ : CompanionTheory.D.DSIC.ActQ := by
  intro n ε H _ _ σ S E h u v
  exact GlobalTheory.CapelliFreeAction.actU_qdet n ε H σ S E (fun a b w => h.act a b w) u v

end GlobalTheory.CompanionTheory.DSCapelliAction
