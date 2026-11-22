module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColEmpty
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.HfNormLeTwo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PerFactor
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaN
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchy
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PaThDiffLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaS
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExtAllInputs
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.GreedySplittingPrincipalTorusExistsStatement
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CharStatementHolds

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory.ThetaTorus

theorem gSup_holds : GSupStatement := gSup GlobalTheory.packingCount

theorem propA_holds : PropAStatement := propA GlobalTheory.packingCount GlobalTheory.gaussTail_of_card_le

theorem dim_holds : DimStatement := dim

theorem J_holds : JStatement :=
  jOf GlobalTheory.ext_all_inputs GlobalTheory.T.greedy_splitting_principal_torus_exists GlobalTheory.charStatement_holds
    (colTorus GlobalTheory.ext_all_inputs propA_holds gSup_holds)
    (colAbel GlobalTheory.ext_all_inputs propA_holds gSup_holds)
    (colEmpty GlobalTheory.ext_all_inputs propA_holds gSup_holds)

theorem N_holds : NStatement := lemmaN dim_holds

theorem I_holds : IStatement := iOf J_holds N_holds

end GlobalTheory.ThetaTorus
