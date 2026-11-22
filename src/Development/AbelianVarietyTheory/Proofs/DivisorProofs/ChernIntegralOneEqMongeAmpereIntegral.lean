module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
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
namespace GlobalTheory

theorem chernInt_one_eq_mInt : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧ ∀ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = mInt A (fun _ => φ.locPot) (fun _ => 1) := by
  intro Y L φ h
  haveI : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace _ Y.isProjOver
  haveI : T2Space (CxPts Y.str (RingHom.id ℂ)) := t2Space_cxPts_of_isProjOver _ Y.isProjOver
  haveI : SecondCountableTopology (CxPts Y.str (RingHom.id ℂ)) :=
    secondCountableTopology_of_isProjOver _ Y.isProjOver
  have hA₀ := AnRead.isAlgAtlas_finAtlas (AnRead.all Y.str (RingHom.id ℂ) Y.dim)
  have hi : φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) :=
    (h.chernInt_eq_mInt_of_isAlgAtlas hA₀ measurable_const).1.2
      (mIntegrableCont _ _
        (fun _ => ((Weight.isCInf_iff_isSmooth hA₀.anRead).1 h).isPotential hA₀) _ continuous_const)
  exact ⟨hi, fun A hA => (h.chernInt_eq_mInt_of_isAlgAtlas hA measurable_const).2 hi⟩

end GlobalTheory
