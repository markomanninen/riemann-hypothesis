module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalLinkConjugateMemIntegralRealPoints
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
theorem _root_.GlobalTheory.T.rationalLink_conjugate_mem_integralRealPoints : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) → ∃ x : X.B.I.GA, Formalism.L2.SG.TermOp.RatLink X x ((W.δ u)⁻¹ * n * W.δ u) ∧ x.1 ∈ Formalism.L2.SG.TermOp.ROinf s := by
  first | exact @GlobalTheory.CoverAct.ratLink_mem_ROinf | exact GlobalTheory.CoverAct.ratLink_mem_ROinf | (intros; apply GlobalTheory.CoverAct.ratLink_mem_ROinf <;> assumption)
