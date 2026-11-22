module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupPropertyClosedMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroElementReduction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagSupportSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselAdaptedTranslateLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLevelReductionCriterion
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPatOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondModelFinitePartFrameActionMatrixStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartNonempty
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NLevelHolds
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsTransportAdelicCorrection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateSymmetricUnipotentPattern
public import Formalism.LocalToGlobal.Divisibility.DefGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceReductionsConjOfNestedFrameStabilisersStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionIffPattern
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentSubMulComplementEqComplement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentBesselCharacterLaws

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChrMatch

variable {D : D7}

theorem suppAt_conj (e : AE D) (V : HSp D) (a n : GA D V) (hn : Formalism.L2.Theta.SuppAt e V n) :
    Formalism.L2.Theta.SuppAt e V (a * n * a⁻¹) := by
  have h1 : Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 =
      Formalism.L2.Theta.mt V a * (Formalism.L2.Theta.mt V n - 1) * Formalism.L2.Theta.mt V a⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  have h2 : (e + cA D e) • (Formalism.L2.Theta.mt V n - 1) = Formalism.L2.Theta.mt V n - 1 := by
    ext i j; exact hn i j
  intro i j
  have h3 : (e + cA D e) • (Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1) = Formalism.L2.Theta.mt V (a * n * a⁻¹) - 1 := by
    rw [h1, ← Matrix.smul_mul, ← Matrix.mul_smul, h2]
  exact congrFun (congrFun h3 i) j

theorem levChi_mul (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {k k' : GA D V}
    (hk : k ∈ levS V β L) (hk' : k' ∈ levS V β L) : levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  have := (levChar D.sp.cm V.gram β L).map_mul ⟨finE V k, hk.2⟩ ⟨finE V k', hk'.2⟩
  unfold levChi
  rw [map_mul, ← Units.val_mul]
  exact congrArg Units.val this

theorem levChi_of_red_one (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (hs : L.s = 0)
    (hQ : L.Q = ∅) {k : GA D V} (hk : ∀ PP ∈ L.Pg, redFn β PP (finE V k) = 1) : levChi V β L k = 1 := by
  have h1 : rTup β L (finE V k) = 1 := by
    funext PP
    show upperLeftBlock L.hr (redFn β PP.1 (finE V k)) = 1
    rw [hk PP.1 PP.2]; exact blockDiagonalExtendByOnePrimeField_one _ _
  unfold levChi levFn
  rw [h1, blockDiagonalExtendByOnePrimeField_one, hs, hQ]
  simp

end GlobalTheory.ChrMatch

end
