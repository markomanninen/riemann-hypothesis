module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjFrameMatrixReindex
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
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
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualFrameConjIntegralSmulOfIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameIdempotentCutMatrixMemStabiliserReductionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteEmbeddingIdempotentPatchInFrameStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjWeilDatumViaAdjointExchangedPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLIffIsUnitDetAtPrime
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseEqOfSameIdempotentPrime
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemAtConjOfOtherPrimeOverSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_conj_frameMatrix_reindex : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → (∀ i j, q.prF he ((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D)).val i j) = gk.val (σ i) (σ j)) ∧ ∀ i j, q.prF he (((β⁻¹ * Lev.finE V (b⁻¹ * g * b) * β : GL (Fin V.rank) (Lev.EAf D))⁻¹).val i j) = (gk⁻¹).val (σ i) (σ j) := by
  first | exact @GlobalTheory.Lev.conj_frame_matrix | exact GlobalTheory.Lev.conj_frame_matrix | (intros; apply GlobalTheory.Lev.conj_frame_matrix <;> assumption)
