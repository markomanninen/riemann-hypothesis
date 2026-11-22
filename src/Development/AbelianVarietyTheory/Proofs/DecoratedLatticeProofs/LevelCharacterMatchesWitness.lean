module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.CarriedPlMap
public import Formalism.LocalToGlobal.SelSide
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivRows3GIff
public import Formalism.LocalToGlobal.Divisibility.ColPins
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem twistedAdelicData_characters_eq_frame (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) (j : Fin B.R.m) :
    Formalism.IndefR.Links.ChrEq (D := (w.st Z).toD7) (a.x.R.mu0 ((j : ℕ) + 1)) (w.I.C.mu0 j) := by
  have h1 : a.x.R.C = Fr.at (w.st Z) f := eq_of_heq (R3.twArgs_lev K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t a).1
  have h2 := a.x.pins.char.base.lev.mu0 j
  have h3 : a.x.R.C.mu0 j = w.I.C.mu0 j :=
    (congrArg (fun C => C.mu0 j) h1).trans (congrArg (fun g : Fr B.toPre => g.mu0 j) w.C_eq).symm
  exact h3 ▸ h2

end GlobalTheory.Fam
