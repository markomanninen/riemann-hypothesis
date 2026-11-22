module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaPartialFourierIntegralMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP

@[expose] public section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ikedaPartialFourierIntegral_mem_adelicSchwartz : ∀ (D : D7), ∀ θ : InfFam D, IsInfFam θ → ∀ (T T' : HSp D) (t n : ℕ) (d : HypDec T T' t) (μ : Measure (Mx D t n)) (𝓕 : Set (Mx D t n)), IsCovolOne (ratMx D t n) μ 𝓕 → ∀ Φ ∈ schwartzA θ T.rank n, ikS d μ Φ ∈ schwartzA θ T'.rank n := by
  first | exact @GlobalTheory.RegSch.IkSchwartz.ikS_mem_schwartzA | exact GlobalTheory.RegSch.IkSchwartz.ikS_mem_schwartzA | (intros; apply GlobalTheory.RegSch.IkSchwartz.ikS_mem_schwartzA <;> assumption)
