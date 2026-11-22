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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevTruePackOfPart
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CornerCoordinateAutomatic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PackB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UsedAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealTB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.BundleLev
theorem lev_of_btw_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) (y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x) :
    (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Pg = x.R.Pg ∧ ∀ t, (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).xiH t = x.R.toLevCh.xiH (x.Y.tupT ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) := by
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y →
      k.B.Q.Rl.toRealDat.Pg = x.R.Pg ∧ ∀ t, k.B.Q.Rl.toRealDat.xiH t = x.R.toLevCh.xiH (x.Y.tupT (k.P.I.tup t)) := by
    intro k hk
    subst hk
    refine ⟨rfl, fun t => ?_⟩
    exact (congrArg x.R.toLevCh.xiH (x.Y.tupT_tup t)).symm
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq
set_option maxHeartbeats 1000000 in
theorem pg_eq_vGs_and_xiH_eq_xi_of_twArgs {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) (x : R3.TwIn q.O.ex)
    (a : R3.TwArgs q.O.ex q.x.what₂) (ax : HEq a.x x) :
    x.R.Pg = (q.B.primes q.w.px).vGs ∧
      ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) μ → x.R.toLevCh.xiH (x.Y.tupT μ) = q.w.I.xi μ := by
  have h := GlobalTheory.Mem.R3.twArgs_lev K _ _ _ q.w q.Z _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have e : a.x = x := eq_of_heq ax
  subst e
  exact ⟨eq_of_heq h.2.1, fun μ hμ => eq_of_heq (h.2.2.1 μ hμ).2⟩
set_option maxHeartbeats 1000000 in
theorem levTrue_packB_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → _root_.GlobalTheory.Fam.LevelCondition' (_root_.GlobalTheory.Fam.packB_alt b) := by
  intro hL p K q c b hw
  have h1 := _root_.GlobalTheory.Fam.BundleLev.lev_of_btw_alt b hw.x hw.y
  have h2 := _root_.GlobalTheory.Fam.BundleLev.pg_eq_vGs_and_xiH_eq_xi_of_twArgs q hw.x hw.a hw.ax
  have hPg : (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Pg = (q.B.primes q.w.px).vGs := h1.1.trans h2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hPg]
    exact ColTest.isTypePlaces_vGs q.w.I q.w.l q.Z q.w.ok
  · intro PP
    rw [hPg]
    exact Iff.rfl
  · intro t
    exact (h1.2 t).trans (h2.2 _ (_root_.GlobalTheory.MiS.Check.used_all_alt (_root_.GlobalTheory.Fam.packB_alt b) t))
end GlobalTheory.Fam.BundleLev
end
