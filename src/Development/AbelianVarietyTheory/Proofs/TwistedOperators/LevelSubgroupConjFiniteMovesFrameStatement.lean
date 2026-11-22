module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelSubgroup_conj_finite_moves_frame : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank) (t : GA D V), t ∈ GfC V → ∀ k : GA D V, (k ∈ levS V β L ↔ t * k * t⁻¹ ∈ levS V (finE V t * β) L) ∧ levChi V (finE V t * β) L (t * k * t⁻¹) = levChi V β L k := by
  first | exact @GlobalTheory.FrameConj.levS_conj_frame | exact GlobalTheory.FrameConj.levS_conj_frame | (intros; apply GlobalTheory.FrameConj.levS_conj_frame <;> assumption)
