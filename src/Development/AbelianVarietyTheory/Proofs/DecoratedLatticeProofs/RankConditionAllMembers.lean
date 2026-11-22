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
public import Formalism.PeriodIntegrals.WeylProd
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WeylProd
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LwRankTies
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstTypePrimeLargeOfRecord

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.MemberCount

theorem rankMu_of_cols (D : D7) (Lv : LevelData D) (C : Formalism.L2.Forms.ColsTiedSym D) (hDu : StandardLattice.FactDuStar D)
    (u : D.what₂.Word) : GlobalTheory.Core.Rk.RankMu D u := by
  have h4 := Formalism.MainNotions.StandardLattice.HarishChandraReduction.rankFormula_of_classNumber D Lv (GlobalTheory.ColClassNumber.classNumber_all D Lv)
  have hr := h4 (GlobalTheory.first_type_prime_large_of_record D) (Formalism.MainNotions.Ext.Lw.splitsF_g_all D) u
    (Formalism.MainNotions.Ext.Lw.splitsF_T_all D u) (Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u)
  have hfin : Module.finrank ℂ (D.s.Cu u) = Module.finrank ℂ (D.mem u).A.Mu0 := (D.s_Cu u).finrank_eq
  unfold GlobalTheory.Core.Rk.RankMu GlobalTheory.Core.Rk.d0
  rw [hfin, hDu u]
  exact hr

end GlobalTheory.Fam.MemberCount
