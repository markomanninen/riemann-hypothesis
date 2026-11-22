module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeIdxUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.XiEqXiOffMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Formalism.LocalToGlobal.IndefiniteReal.RealRec
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BaseMatrixGlApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemFiniteAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeForward
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeImage
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeKernel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BcPrVMemLevelVLOfMoves
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesLocalSuppIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCoordinateVectorsChainSpaceSelfDual
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletion
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLastRowCongrOneMemLocalLevelLevelPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMatrixEntryIntegralOfKeepsStandardLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCompactLevelProperty
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixEntryIntegralityCongruence
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalIndex
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalRelation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalProperty
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CarriesLatticeCompletionOnOffIffAllFinitePlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesOfMatrixMemLevelZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameReorderingLevelData

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

namespace GlobalTheory.FamTraceChiCol


open GlobalTheory.StepData GlobalTheory.RootEx GlobalTheory.SymChain in
theorem conj_embX_toBlocks₂₂ {k : Type} [Field k] {ι n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (g : GL n k) :
    ((typeFrame ϖ ord).bas⁻¹ * embX c g * (typeFrame ϖ ord).bas).val.toBlocks₂₂ = 1 := by
  have e1 : (typeFrame ϖ ord).bas.val = fromBlocks 1 0 0 (GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1)).val := rfl
  have e2 : ((typeFrame ϖ ord).bas⁻¹).val =
      fromBlocks 1 0 0 ((GlobalTheory.SplitFlip.diagGL fun i : Fin c => ϖ ^ (i.val + 1))⁻¹).val := by
    change (embA n _)⁻¹.val = _
    rw [← map_inv]; rfl
  rw [Units.val_mul, Units.val_mul, e1, e2, show (embX c g).val = fromBlocks g.val 0 0 1 from rfl,
    fromBlocks_multiply, fromBlocks_multiply]
  simp only [toBlocks_fromBlocks₂₂, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul,
    Units.inv_mul]

end GlobalTheory.FamTraceChiCol

noncomputable section
namespace GlobalTheory.FamTraceChiCol


end GlobalTheory.FamTraceChiCol
end
