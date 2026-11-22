module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalRootCoordinatesEqFrameMatrix
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordCont
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingAffine
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopBPin
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabUMapEqOfRoots

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalRootCoordinates_eq_frameMatrix : ∀ (D : D7) (X : HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ s y : X.B.I.Ginf) (τ : D.what₂.Tau) (M : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat ((γ⁻¹ * (s⁻¹ * y * s) * γ) (X.pl.symm τ))) (Formalism.L2.SG.RealObj.frm X u' 1 (X.pl.symm τ)) M → ∀ q : GlobalTheory.LoopV.roots (ptMat w), GlobalTheory.LoopVol.ratCoord X u' w γ s y τ q = M q.1.1 q.1.2 := by
  first | exact @GlobalTheory.LoopVol.ratCoord_eq_matOn | exact GlobalTheory.LoopVol.ratCoord_eq_matOn | (intros; apply GlobalTheory.LoopVol.ratCoord_eq_matOn <;> assumption)
