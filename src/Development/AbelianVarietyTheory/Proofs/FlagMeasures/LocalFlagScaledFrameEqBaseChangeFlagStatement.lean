module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFlagScaledFrameEqBaseChangeFlag
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Ia

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_flag_scaled_frame_eq_baseChange_flag : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ (p : PlF D) (j : ℕ), Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (G.fl.Xa j : Set (VS D).V)) = (A p).Fj j := by
  first | exact @GlobalTheory.FlagBaseChange.span_bcP_Xa_eq_Fj | exact GlobalTheory.FlagBaseChange.span_bcP_Xa_eq_Fj | (intros; apply GlobalTheory.FlagBaseChange.span_bcP_Xa_eq_Fj <;> assumption)
