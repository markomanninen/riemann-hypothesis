module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoeffEqZeroOfDistinctEigencharacters
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilMatrixCoeff_eq_zero_of_distinct_eigencharacters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (m : Measure (WO S T)) (X : Set (WO S T)), IsCovolOne (ratL T S) m X → ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F →
    ∀ (g : GA D T) (y : WO S T) (a b : AF D.host.F), heisO ψ S T y F = ψ a • F →
    heisO ψ S T (actO S T 1 g⁻¹ y) F = ψ b • F → ψ a ≠ ψ b → ∫ w in X, om (1, g) F w * conj (F w) ∂m = 0 := by
  first | exact @GlobalTheory.TargetCoef.coef_zero_of_target_eigen | exact GlobalTheory.TargetCoef.coef_zero_of_target_eigen | (intros; apply GlobalTheory.TargetCoef.coef_zero_of_target_eigen <;> assumption)
