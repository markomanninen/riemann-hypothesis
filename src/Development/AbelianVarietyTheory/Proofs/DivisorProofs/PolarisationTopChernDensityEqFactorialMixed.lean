module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatLinearCombination
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationDetStatement

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem pol_chernDens_comb : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → HermLB p) (c : AlgChart p σ D), ∀ y ∈ c.e.source, FibreProj.pol (fun n => c.chernDens ((ArInt.comb L n).φ σ) y) = D.factorial * dens (fun i => MLine.ofHerm (L i) σ) c y := by
  intro k _ X p σ D L c y hy
  set H : Fin D → Matrix (Fin D) (Fin D) ℂ := fun j => MixDens.chernMat ((L j).φ σ) c y with hH
  have hc (n : Fin D → ℤ) : c.chernDens ((ArInt.comb L n).φ σ) y =
      D.factorial / Real.pi ^ D * (∑ j, (n j : ℂ) • H j).det.re := by
    rw [← MixDens.chernMat_comb k X p σ D (Fin D) L n c y hy]
    rfl
  have key := GlobalTheory.T.sum_neg_one_pow_card_det_sum_eq_sum_perm_det D H
  simp only [FibreProj.pol, hc, dens, MLine.ofHerm]
  have e2 : (∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => c.hess ((L (τ l)).φ σ) (pick ((L (τ l)).φ σ).isLB y) y j l).det)
      = ∑ τ : Equiv.Perm (Fin D), (Matrix.of fun j l => H (τ l) j l).det := rfl
  rw [e2, ← key, Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  have : ((-1 : ℂ) ^ S.card) = (((-1 : ℝ) ^ S.card : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  trans (-1) ^ S.card * (D.factorial / Real.pi ^ D * (∑ i, (if i ∈ S then (-1 : ℂ) else 0) • H i).det.re)
  · simp only [apply_ite (Int.cast : ℤ → ℂ), Int.cast_neg, Int.cast_one, Int.cast_zero]
  · ring

end GlobalTheory.Mix
