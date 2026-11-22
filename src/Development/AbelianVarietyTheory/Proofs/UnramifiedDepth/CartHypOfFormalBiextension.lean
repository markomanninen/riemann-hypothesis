module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
public import Formalism.LocalToGlobal.CharacterGerms.NegMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfIntegralGaugedFormalGroupLawStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsPairDataStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawPairDataStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndPairPlacesStatement

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory

theorem cartHyp_of_formalBiextension : CartFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p
  exact GlobalTheory.T.cartHyp_of_integralGaugedFormalGroupLaw C V d I (Fin dd) (Y.raw p) (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_pairData C V O dd Y d I p)
    (GlobalTheory.T.hasGaugeAdjointLieProjectors_pairData C V O dd Y d I p) (GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_pair_places C V O dd Y d I p)

end GlobalTheory
