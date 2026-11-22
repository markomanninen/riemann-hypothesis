module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
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
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
public import Development.AutomorphicArithmetic.CharacterBoxes.ExS
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceScalarsErrorsReadings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IotaStarProjectionQsp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionPairingRationalOnRationalPoints

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 4000000 in
theorem readC_reFace_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X0 : BaseLevelRowSide D)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp Sp' : ∀ Zs, SPer (Dc Zs))
    (Zsc Zsc' : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (kap : ℝ) (lam : type_of% R.lam3)
    (err : type_of% (R.updS kap lam).err0) {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
    (C : ReadC R (reFace F Dc Sp Zsc) X0 Y)
    (Y₁ : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat F.lv2 X0) (h1 : Y₁.tup = Y.tup) (h2 : HEq Y₁.jA Y.jA) :
    Nonempty (ReadC ((R.updS kap lam).withErr err) (reFace F Dc Sp' Zsc') X0 Y₁) := by
  have key : ∀ (tp : T → D.what₂.Tup)
      (j : ∀ t, (Fin (rDim D A3.A F.P1 F.ψ1 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tp t)), tp = Y.tup → HEq j Y.jA →
      ∀ (u : D.what₂.Word) (t : T) (x : Fin ((Dc (R.toCx3 F).zs).a (C.wU u)) → D.what₂.LL)
        (f : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV t) → D.what₂.LL),
        D.what₂.embLL ((Dc (R.toCx3 F).zs).Pt (C.wU u) t x f) =
          D.what₂.perCol u (tp t) (D.jN u (C.eNu u x)) (j t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)) := by
    intro tp j h1 h2
    subst h1
    cases h2
    exact C.pt
  exact ⟨⟨C.wU, C.bij, C.eNu, C.NuC, C.nu, key Y₁.tup Y₁.jA h1 h2⟩⟩

end GlobalTheory.Mem.R3

