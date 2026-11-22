module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearUniformisationOfCompleteDvrStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationUnconditionaStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_pelUnif_of_cdvr_unconditional :
    ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (t : SAB H (Sp V)) (A : PolAV (Sp (FractionRing V))) (gen : (Over.pullback (jK V)).obj t.G ≅ A.A), IsMonHom gen.hom → (∃ w : LB.Iso (A.L.pull gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK V))), w.IsGen) → (∃ S : SplitExt (Sp (IsLocalRing.ResidueField V)), S.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj t.G)) → ∃ P : PELUnif (maximalIdeal V) t, P.A = A ∧ HEq P.U.gen gen ∧ P.TorsionIso :=
  GlobalTheory.T.exists_linearUniformisation_of_complete_dvr GlobalTheory.T.exists_degenerationData_uniformisation_unconditional GlobalTheory.T.all_six_abelian_scheme_laws_hold.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.1
    GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.2.1 GlobalTheory.T.all_six_abelian_scheme_laws_hold.2.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.2.2

end GlobalTheory.UU
