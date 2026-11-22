module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEndomorphismsToCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GaloisHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AdmissibleBasePowerSeries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTriplesTorsionStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLawsStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

section Factor

open GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_tau_four (D : DegPre R) (a b : D.X) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (lamPts (toUnit (TK R) ≫ D.c a) (toUnit (TK R) ≫ D.c b)) negε), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J), Good D.P.L z J → val t r z J = val (D.tau a b) r z J := by
  refine exists_gen D.P.isLB ?_ (D.tau a b) (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (D.psi_gen _)
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (D.psi_gen _))) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (D.psi_gen _)))
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ D.rig_gen _)))
  intro U _ h
  have e : toUnit (TK R) ≫ D.c (a + b) = (toUnit (TK R) ≫ D.c a) * (toUnit (TK R) ≫ D.c b) := by
    rw [D.c_add]; exact MonObj.comp_mul _ _ _
  simp only [Fintype.prod_sum_type, Fin.prod_univ_four, lamPts, negε, ← e]
  simp [eSec, Hom.one_def]

end Factor
end GlobalTheory.Mum
