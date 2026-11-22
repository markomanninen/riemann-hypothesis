module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneLeDimAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainMeasureNeTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLowestKTypeWeylDimensionLeOfSizeBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFramesStrongApproximationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaTermTsumLeTwo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupMeasureDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentificationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamily
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

namespace GlobalTheory.OneMeasureRatio

theorem log_r_add_three_le (D : D7) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L) :
    Real.log ((D.R.r : ℝ) + 3) ≤ L := by
  have hr : 6 ≤ D.R.r := by
    unfold Ranks.r; have := D.R.two_le_m; have := D.R.m_add_three_le_k; omega
  have hf : 2 ≤ D.R.f := by
    unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) D.R.ord_pos; omega
  have hn : D.R.r ≤ D.R.nV := by unfold Ranks.nV; omega
  have hr' : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr
  have hf' : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hn' : (D.R.r : ℝ) ≤ D.R.nV := by exact_mod_cast hn
  have h1 := hL.1
  rw [← Real.log_exp L]
  refine Real.log_le_log (by positivity) ?_
  have a1 : 2 * (D.R.r : ℝ) ≤ (D.R.f : ℝ) * D.R.r := mul_le_mul_of_nonneg_right hf' (by positivity)
  have a2 : 2 * (D.R.r : ℝ) * D.R.r ≤ (D.R.f : ℝ) * D.R.r * D.R.nV :=
    mul_le_mul a1 hn' (by positivity) (by positivity)
  have : (D.R.r : ℝ) + 3 ≤ (D.R.f : ℝ) * D.R.r * D.R.nV := by nlinarith
  linarith

end GlobalTheory.OneMeasureRatio
