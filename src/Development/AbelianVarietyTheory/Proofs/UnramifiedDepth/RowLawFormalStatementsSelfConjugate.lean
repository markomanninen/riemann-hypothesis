module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
public import Formalism.LocalToGlobal.CharacterGerms.NegMem
public import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfIntegralGaugedFormalGroupLawStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLawStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermsIndependentOfCurveSystem
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsSelfConjugatePlaceStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupKernelSmallOfSecondStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquarStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndSelfConjugatePlaceStatement

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem formal_statements_selfConj :
    CartSelfSt ∧ AxesSelfSt ∧ GermZeroSelfConjugate ∧ CEqSelfSt ∧ IndependenceBoundSelfConjugate := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact GlobalTheory.T.cartHyp_of_integralGaugedFormalGroupLaw C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p) (GlobalTheory.T.hasGaugeAdjointLieProjectors_selfConjugatePlace C V O dd Y d I0 p)
      (GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_selfConjugatePlace C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    have h := GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p
    exact RawChart.axes_of _ h.exc h.axes
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact intGerm_indep_of_rlaw C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p _
    exact GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact GlobalTheory.T.gaugedFormalGroup_kernel_small_of_second C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p)

end GlobalTheory.RowLaw
