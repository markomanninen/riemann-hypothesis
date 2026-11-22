module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVarietyStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationOfTorsionCouStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionEqOfLawsStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThmUOfAllSet

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZH

theorem thmU_and_uTors : GlobalTheory.ZH.ThmUSt ∧ GlobalTheory.ZH.UTorsSt := by
  obtain ⟨L, L2, L3, L4, L5, -⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
  refine ⟨GlobalTheory.ZH.thmU_of_allSet L GlobalTheory.homExtension_semiAbelian_dvr (by
    have h := GlobalTheory.T.exists_degenerationData_uniformisation_of_torsionCount (GlobalTheory.T.card_torsion_points_abelianVariety L.globalFns L.rigidity) L L2
    intro V _ _ _ A G _ _ s
    obtain ⟨D, U, -, hg, -⟩ := h V A G s
    exact ⟨D, U, hg⟩), GlobalTheory.T.uniformisation_torsion_eq_of_laws L L2 L3 L4 L5⟩

end GlobalTheory.ZH
