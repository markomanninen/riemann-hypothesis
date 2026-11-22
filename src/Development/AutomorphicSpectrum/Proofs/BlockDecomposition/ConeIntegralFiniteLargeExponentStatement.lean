module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeIntegralFiniteLargeExponent
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLocallyFiniteContinuous
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoFrameFirstCols

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_integral_finite_large_exponent : ∀ (F : Type) [Field F] [NumberField F] (n r : ℕ) (c : ℝ), 0 < c → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    ∫⁻ t in cone r c, ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.ConeInt.lintegral_cone_lt_top | exact GlobalTheory.CompanionTheory.ConeInt.lintegral_cone_lt_top | (intros; apply GlobalTheory.CompanionTheory.ConeInt.lintegral_cone_lt_top <;> assumption)
