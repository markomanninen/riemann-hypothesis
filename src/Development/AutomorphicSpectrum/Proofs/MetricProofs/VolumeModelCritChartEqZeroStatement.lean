module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.VolumeModelCritChartEqZero
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPtsBddConv
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETailMass
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreFinite
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeI
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocDensDivJacN

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_modelCrit_chart_eq_zero : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Q : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (j : Fin M.atlas.n), IsArithVar P (n + 1) → IsGoodProj P Q → volume ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' modelCrit M Q) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit.modelCrit_null | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit.modelCrit_null | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.Crit.modelCrit_null <;> assumption)
