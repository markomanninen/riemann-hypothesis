module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceFormFlagPairingIntegralOnFrameLatti
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemDeeperLevelIffReductionsSymmetricUnipotentStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
public import Formalism.LocalToGlobal.Divisibility.TiedLemmas

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.otherInstanceForm_flagPairing_integral_on_frameLattice : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (β : GL (Fin (Yc D 0).rank) (EAf D)), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ (PP : Pl D.host.E) (a : Fin (Yc D 0).rank) (z : Fin (Yc D 0).rank → EAf D), (∀ i, Matrix.mulVec (β⁻¹).val z i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → GlobalTheory.SeeConjChar.hT X h (pairAt X h PP a) z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.SeeConjChar.hT_pairAt_int | exact GlobalTheory.SeeConjChar.hT_pairAt_int | (intros; apply GlobalTheory.SeeConjChar.hT_pairAt_int <;> assumption)
