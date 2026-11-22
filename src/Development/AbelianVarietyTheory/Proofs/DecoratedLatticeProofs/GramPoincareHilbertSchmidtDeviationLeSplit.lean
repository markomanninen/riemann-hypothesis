module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNormSqOrthonormalLeHilbertSchmidt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ExpQuarterMulExpQuarterLeTwo
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CorankOneIsEquivalenceOnRow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Rk

theorem hsNormSq_add_le_three_halves {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A B : Wq →L[ℂ] Wp) :
    hsNormSq (A + B) ≤ 3 / 2 * hsNormSq A + 3 * hsNormSq B := by
  rw [hsNormSq_eq, hsNormSq_eq, hsNormSq_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_add_le (A (stdOrthonormalBasis ℂ Wq i)) (B (stdOrthonormalBasis ℂ Wq i))
  have h0 := norm_nonneg (A (stdOrthonormalBasis ℂ Wq i) + B (stdOrthonormalBasis ℂ Wq i))
  rw [ContinuousLinearMap.add_apply]
  nlinarith [sq_nonneg (‖A (stdOrthonormalBasis ℂ Wq i)‖ - 2 * ‖B (stdOrthonormalBasis ℂ Wq i)‖)]

theorem hsDev_le_split_three_halves : ∀ (D : D7) (u : D.what₂.Word), GlobalTheory.Core.Rk.hsDev D u ≤
    3 / 2 * hsNormSq (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + 3 * hsNormSq (AdmissibleBoundsFromSource.Kpp D u u) := by
  intro D u
  have e : Kmat D.s u u - ContinuousLinearMap.id ℂ (D.s.Cu u) =
      (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + AdmissibleBoundsFromSource.Kpp D u u := by abel
  unfold GlobalTheory.Core.Rk.hsDev
  rw [e]
  exact hsNormSq_add_le_three_halves _ _

end GlobalTheory.Core.Rk
