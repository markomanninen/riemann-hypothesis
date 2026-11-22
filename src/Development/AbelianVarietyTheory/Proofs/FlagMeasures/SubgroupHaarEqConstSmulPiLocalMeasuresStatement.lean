module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SubgroupHaarEqConstSmulPiLocalMeasures
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.Pf.AmpWinLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subgroupHaar_eq_const_smul_pi_localMeasures : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ X.muH u = κ • Measure.pi (fun v => muHl C u (X.pl v) v) := by
  first | exact @GlobalTheory.MuHPi.muH_eq_pi | exact GlobalTheory.MuHPi.muH_eq_pi | (intros; apply GlobalTheory.MuHPi.muH_eq_pi <;> assumption)
