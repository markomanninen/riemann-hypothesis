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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SquareIntegrableColumnsTied
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.MiS
namespace GlobalTheory.Fam
@[reducible] def packB_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : _root_.GlobalTheory.MiS.RealPackAlt O.ex :=
  letI := b.B.alg
  { R := b.R, S := b.S, P := b.P, Dcf := b.C.c.face, Spf := b.C.Sp, Zscf := GlobalTheory.Fc.zsc b.P b.DH.1.1 b.DH.1.2 c,
    Ks := b.B.T.Q.c.F, Q := b.B.Q }
structure BundlePointConditions {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) : Prop where
  join : Nonempty (_root_.Formalism.L2.SG.JoinSI.IndefiniteRealisationJoin b.R b.S b.B.Q)
  dc : DcPtG b.P
  frames : _root_.Formalism.IndefR.IndefiniteRealisation.FramesEx b.B.Q
  see : _root_.Formalism.IndefR.IndefiniteRealisationExtends b.B.Q
  ex : b.B.Q.Rl.toRealDat.ExAt
  prim : Formalism.IndefR.Links.PrimRows3 b.B.Q.Rl b.B.Q.F ∧ b.P.A3.fam3.TypesSep3
  fin : Formalism.L2.SG.PackageTie2.FinX b.S.Y
  gapS : GlobalTheory.Count.GapGe b.S.X.B (100 * (D.R.r : ℝ) ^ 4)
  gap : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D
  rS : 1 ≤ D.R.rS
end GlobalTheory.Fam
end
end
