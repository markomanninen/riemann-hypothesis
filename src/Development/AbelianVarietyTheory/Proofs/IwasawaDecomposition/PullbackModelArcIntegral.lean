module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelPointsEqOfSameDegenerationData
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.AdmissibleBasePowerSeriesSpanX
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsOpenImmersionJKPowerSeries
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabDescentOfFieldExtension
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIntegrallyClosedPowerSeries
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrameOfFreeSec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcDataPsiValuationEqHalfForm
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ScaleGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MoveQkCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef
open MonoidalCategory CartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ArcChartExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem sabMap_cast_φ {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f₁ f₂ : S' ⟶ S} (h : f₁ = f₂)
    (n : SABMap t' t f₁) : (h ▸ n).φ = n.φ := by
  subst h; rfl

theorem exists_sab_cancel_id {S S' : Scheme.{0}} {t : SAB H S} {t' t'' : SAB H S'} {f : S' ⟶ S}
    (m : SABMap t' t f) (n : SABMap t'' t f) : ∃ m' : SABMap t'' t' (𝟙 S'), n.φ = m'.φ ≫ m.φ := by
  obtain ⟨m', hm'⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := 𝟙 S') m ((Category.id_comp f).symm ▸ n)
  exact ⟨m', (sabMap_cast_φ (Category.id_comp f).symm n).symm.trans hm'⟩

end GlobalTheory.ArcChartExt
