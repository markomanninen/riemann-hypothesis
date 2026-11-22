module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntriesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TsumAdelicMatrixSchwartzMajorantRationalNeTopStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctionsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelHeisenbergPhaseEqCexpRealPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SupNormWordSumSubLeAndDerivativeCost
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartEqSumTraceTraceDualBasis

namespace I195MixedCoordinates_6edf13e9c2ea736a34004c3c

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_6edf13e9c2ea736a34004c3c

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

noncomputable section

namespace GlobalTheory.Unf.DoubleSum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

section Source

variable {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ)

theorem mixS_add (hψ : IsStdChar D ψ (-1)) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (x : Mx D T.rank ρ) : (_root_.I195MixedCoordinates_6edf13e9c2ea736a34004c3c.source d) T ψ v.μ v.𝓕 (f + g) x = (_root_.I195MixedCoordinates_6edf13e9c2ea736a34004c3c.source d) T ψ v.μ v.𝓕 f x + (_root_.I195MixedCoordinates_6edf13e9c2ea736a34004c3c.source d) T ψ v.μ v.𝓕 g x := by
  funext w
  have h1 := d.integrableOn_mixS hψ.1.1 v.covol hf x w
  have h2 := d.integrableOn_mixS hψ.1.1 v.covol hg x w
  change d.mixS T ψ v.μ v.𝓕 (f + g) x w = d.mixS T ψ v.μ v.𝓕 f x w + d.mixS T ψ v.μ v.𝓕 g x w
  simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.add_apply, mul_add] at h1 h2 ⊢
  exact integral_add h1 h2

theorem mixS_smul (c : ℂ) (f : WO S T → ℂ) (x : Mx D T.rank ρ) :
    (_root_.I195MixedCoordinates_6edf13e9c2ea736a34004c3c.source d) T ψ v.μ v.𝓕 (c • f) x = c • (_root_.I195MixedCoordinates_6edf13e9c2ea736a34004c3c.source d) T ψ v.μ v.𝓕 f x := by
  funext w
  change d.mixS T ψ v.μ v.𝓕 (c • f) x w = c • d.mixS T ψ v.μ v.𝓕 f x w
  simp only [HypDec.mixS, HypDec.integrandS_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul]


variable (T) in
def dualPt (ρ : ℕ) : Mx D ρ T.rank →+ Mx D T.rank ρ where
  toFun b := adj (incA D D.host.xi0⁻¹ • (b * giA T))
  map_zero' := by rw [Matrix.zero_mul, smul_zero, adj_zero]
  map_add' _ _ := by rw [Matrix.add_mul, smul_add, adj_add]

theorem symplO_dualPt (x : Mx D T.rank ρ) (b : Mx D ρ T.rank) :
    symplO S T (d.extX T x) (d.extY T (dualPt T ρ b)) = Algebra.trace (AF D.host.F) (AE D) (x * b).trace := by
  have h := d.hO_ext T x 0 0 (dualPt T ρ b) 0 0
  simp only [map_zero, zero_add, add_zero, hO_eq_trace S₀, Matrix.mul_zero, trace_zero] at h
  rw [symplO_eq, h, show pairS T (0 : Mx D T.rank ρ) 0 = 0 by simp [pairS], add_zero, pairS]
  congr 1
  rw [show dualPt T ρ b = adj (incA D D.host.xi0⁻¹ • (b * giA T)) from rfl, adj_adj, Matrix.smul_mul, trace_smul, smul_eq_mul, ← mul_assoc, ← map_mul,
    mul_inv_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul, Matrix.mul_assoc, giA_gA_cancel, trace_mul_comm]

end Source

section Target

variable {S T T₀ : HSp D} {σ : ℕ} (d : HypDec T T₀ σ) (v : VolM D σ S.rank)

end Target

section Double

variable {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (d : HypDec S S₀ ρ) (d' : HypDec T T₀ σ) (v : VolM D T.rank ρ)
  (v' : VolM D σ S₀.rank)


end Double

end GlobalTheory.Unf.DoubleSum

end
