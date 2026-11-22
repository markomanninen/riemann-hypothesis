module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVarietyStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenThetaAbelianVariety

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem exists_gen_theta_of_isAbelianScheme :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∀ M : LB B.left, M.IsLB → ∃ t : LB.Gen (Theta B M), t.IsGen := by
  intro K _ _ B _ hB M hM
  have := hB.comm
  exact GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety GlobalTheory.globalFns_holds K B hB (GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety K B hB) M hM

end GlobalTheory
