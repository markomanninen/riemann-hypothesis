module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GeometricGaloisRepCompatibility
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadOfEigenLabeling
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open GlobalTheory.HeightCounting.Fin3 GlobalTheory.HeightCounting.Up.RealOfReading

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.ThirdTied

noncomputable section

variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {K : Ctx} {B : Base} {f : Fr B.toPre}
  {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P}

def idempotentReadingChoice (L : LocAll (lay0 (Dof x)))
    (l : StrictHenselianAcyclicLevel hL x) : NChoice (DL x L) :=
  let c := chL L l.c.ch
  @NChoice.mk (DL x L) c.twI c.twI_l c.sd c.Q c.k' c.psi' c.Oe
    c.crOe c.domOe c.dvrOe c.algOe c.algOOe c.towOe c.Oe_inj c.Oe_fin c.Oe_loc
    c.embW c.embW_w c.eMt c.eMt_basis c.eMt_lat

def idempotentReadingTuple (L : LocAll (lay0 (Dof x)))
    (l : StrictHenselianAcyclicLevel hL x) : TupTied (DL x L) (cfD x L) (idempotentReadingChoice L l) :=
  let tp := tpL L l.c.tp
  @TupTied.mk (DL x L) (cfD x L) (idempotentReadingChoice L l)
    tp.xi tp.xi_inj tp.xi_fin tp.xi_triv tp.xi_tame tp.psi
    tp.trueColumnChoices_heckeChar_reference_eq_one tp.xi_star tp.xi_star' tp.xi_tw
    tp.psi_is tp.psi_un

end

abbrev OrdinaryIdempotentThirdComponent : Prop :=
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
      PublishedInputsThirdLayerAlt → GlobalTheory.NRows.GeometricGaloisRepCompatibility →
      AllSt fun _ _ _ T w P x =>
        ∀ (l : StrictHenselianAcyclicLevel hL x)
          (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))),
          GlobalTheory.CoefDuty.BuiltAlt l.a.A l.mt.M l.c.ch l.c.tp.tup big L →
          SumRepresentations.hypO (withLoc L) →
          ∀ (m : Moved (oL x L)), m.Copy → m.Coh →
          ∀ (s : Side0 (oL x L)) (r : ReadPk m s), r.Pin →
          ∀ (hC : m.z.R.C = cfD x L) (Xd : DivX (DL x L)) (E : EigIdx (DL x L) Xd)
            (labPi : E.Pi → (famR (w.st (oL x L).Z) w.I P.hX
              (usedOf w.I T P.Wt) m.z.Xg m.z.tr).A.fam.base.Ix) hb htup hg hf,
            GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector
              (realOfRead (D := DL x L) m.z.R.toRealDat m.z.F.lv2 r.Y
                (idempotentReadingTuple L l) hC Xd E labPi hb htup hg hf)

theorem ordinary_idempotent_third_component_alt : OrdinaryIdempotentThirdComponent := by
  intro hL _ _
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l big L _ _ m _ _ s r _ hC Xd E labPi hb htup hg hf
  exact IdempotentAdelicReading.goodIdempotent_eq_goodProjector_adelicReading
    m.z.R.toRealDat m.z.F.lv2 r.Y (idempotentReadingTuple L l) hC Xd E labPi hb htup hg hf
    m.intersectionNumber_baseChange.ok.ok2

end GlobalTheory.HeightCounting.Up.ThirdTied

theorem _root_.GlobalTheory.T.ordinary_idempotent_third_component_of_cmDatum_alt :
    GlobalTheory.HeightCounting.Up.ThirdTied.OrdinaryIdempotentThirdComponent :=
  GlobalTheory.HeightCounting.Up.ThirdTied.ordinary_idempotent_third_component_alt

end
