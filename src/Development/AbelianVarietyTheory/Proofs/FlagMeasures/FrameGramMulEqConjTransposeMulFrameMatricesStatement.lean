module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameGramMulEqConjTransposeMulFrameMatrices
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
theorem _root_.GlobalTheory.T.frameGram_mul_eq_conjTranspose_mul_frameMatrices : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (g γ h : X.B.I.Ginf) (v : NumberField.InfinitePlace X.B.I.F) (C B : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ), GlobalTheory.LoopAct.IsMatOn (uMat (g⁻¹ v)) (Formalism.L2.SG.RealObj.frm X u 1 v) C → GlobalTheory.LoopAct.IsMatOn (uMat (h v)) (Formalism.L2.SG.RealObj.frm X u' 1 v) B → Formalism.L2.SG.RealObj.ZX X u u' 1 (g * γ * h) v = Cᴴ * Formalism.L2.SG.RealObj.ZX X u u' 1 γ v * B := by
  first | exact @GlobalTheory.ZxMul.zx_mul | exact GlobalTheory.ZxMul.zx_mul | (intros; apply GlobalTheory.ZxMul.zx_mul <;> assumption)
