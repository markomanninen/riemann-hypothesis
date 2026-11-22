module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceStandardChartFubiniStudy
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Partition
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShift
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PushAFinsumInter
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Measure
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Degree
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projSpace_standardChart_fubiniStudy : ∀ N : ℕ, ∃ (c : AlgChart (PSpace.str ℂ N) (RingHom.id ℂ) N) (i : (ProjSpace.hermitianTwistingSheaf ℂ N).B.ι), c.e.source = ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) (ProjSpace.chart ℂ N 0) ∧ c.e.target = Set.univ ∧ c.e.source ⊆ ptsIn (PSpace.str ℂ N) (RingHom.id ℂ) ((ProjSpace.hermitianTwistingSheaf ℂ N).B.U i) ∧ ∀ v, ((ProjSpace.hermitianTwistingSheaf ℂ N).φ (RingHom.id ℂ)).φ i (c.e.symm v) = Real.log (1 + ‖v‖ ^ 2) := by
  first | exact @GlobalTheory.StdProjChart.exists_stdChart | exact GlobalTheory.StdProjChart.exists_stdChart | (intros; apply GlobalTheory.StdProjChart.exists_stdChart <;> assumption)
