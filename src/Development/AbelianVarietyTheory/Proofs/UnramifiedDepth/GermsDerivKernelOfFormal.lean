module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
public import Formalism.LocalToGlobal.CharacterGerms.NegMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairDataStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermsIndependentOfCurveSystemStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLawStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupKernelSmallOfSecondStatement

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem germs_deriv_kernel_of_formal : IntegralGermIndependentAllCharts ∧ CEqFBSt ∧ IndependenceBoundAllCharts :=
  ⟨fun C _ _ V O _ _ dd Y d _ I _ p H =>
      GlobalTheory.T.integralGerms_independent_of_curveSystem C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p) H,
    fun C _ _ V O _ _ dd Y d _ I _ p _ H =>
      GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p) H,
    fun C _ _ V O _ _ dd Y d _ I _ p hr H h2 =>
      GlobalTheory.T.gaugedFormalGroup_kernel_small_of_second C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p) hr H h2⟩

end GlobalTheory.RowLaw
