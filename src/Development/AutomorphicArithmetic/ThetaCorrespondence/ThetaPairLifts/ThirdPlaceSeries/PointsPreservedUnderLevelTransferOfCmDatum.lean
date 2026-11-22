module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StateB2OfRationalData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataLaterStagesWithNewTwistStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedReadingTransportedNewTwistStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadPackageTwistHeq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesAtThetaTwist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Detects
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSumLeOfLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeUnitOfExportTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitHeckePrimeOffLevelOfHeckeIndexPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeGeometricAllStates
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricHeckeLawsOfMultiplicityLowerBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Lb2OfThetaTwistStatement
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
noncomputable section
namespace GlobalTheory.HeightCounting.Up
open GlobalTheory.Mem.R3.Tr in
theorem points_preserved_under_level_transfer_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ D0 : D7, _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x →
    Carried D0 (Dof x) → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x') ∧ Carried D0 (Dof x') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x' := by
  intro hPr hSer hL
  refine StepW.trans (_root_.GlobalTheory.T.geoLaws_iC_at_levelB1_of_serN hPr hSer hL) ?_
  refine StepW.of_all ?_
  intro K B f T w _ _ hq P x D0 l hC
  have hlaw := hq P x l
  obtain ⟨x', hl', ho, hLc⟩ := _root_.GlobalTheory.T.exists_levelB2_twist_of_thetaTie hL x l (GlobalTheory.GeoTie.geoNTh hlaw) (GlobalTheory.GeoTie.geoTie hlaw)
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at ho
  subst ho
  refine ⟨⟨oTw x (thTw (Dof x) (GlobalTheory.GeoTie.geoNTh hlaw)), fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩, hl',
    carried_thTw D0 (Dof x) _ hC, fun cDep hLs => ?_⟩
  have hgen (D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp)
      (Z : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.IsLamTieFull D.ntw Z →
        GlobalTheory.LamTie.IsLamTieFull (thTw D th).toD7.ntw (lamTw (thTw D th) Z) := fun h => h
  have htrans (y : St P) (N : TwNew (Dof y))
      (hN : ∀ Z : GlobalTheory.LamTie.LamDat (Dof y), GlobalTheory.LamTie.IsLamTieFull (Dof y).ntw Z → GlobalTheory.LamTie.IsLamTieFull N.tw Z)
      (c b : ℝ) {I : Type} (Lc : Formalism.IndefR.Links.LevCh (Dof y) I)
      (h : ListPin (Dof y) Lc c b) :
      ListPin (w.st (oTw y N).Z).toD7 (levCh (a := y.o.Z) (oTw y N).Z Lc) c b := by
    obtain ⟨G, h1, h2⟩ := h
    exact ⟨(by with_unfolding_all exact ((GlobalTheory.Mem.GridMove.gdC (a := y.o.Z) (oTw y N).Z G) :)),
      ⟨(by with_unfolding_all exact (h1.values :)), (by with_unfolding_all exact (h1.roots :))⟩,
      (by with_unfolding_all exact ((hN _ h2) :))⟩
  have eL : m'.z.R.toRealDat.toLevCh =
      (by with_unfolding_all exact ((levCh (a := x.o.Z) (oTw x (thTw (Dof x) (GlobalTheory.GeoTie.geoNTh hlaw))).Z x.m.z.R.toRealDat.toLevCh) :)) := eq_of_heq hLc
  show ListPin _ m'.z.R.toRealDat.toLevCh cDep K.s.b
  rw [eL]
  exact htrans x _ (fun Z h => hgen _ _ Z h) _ _ _ hLs
end GlobalTheory.HeightCounting.Up
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelB2_carried_of_levelB1 : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ P x => ∀ D0 : D7, _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevel hL x → Carried D0 (Dof x) → ∃ x' : St P, Nonempty (_root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x') ∧ Carried D0 (Dof x') ∧ ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x' := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.points_preserved_under_level_transfer_alt | exact _root_.GlobalTheory.HeightCounting.Up.points_preserved_under_level_transfer_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.points_preserved_under_level_transfer_alt <;> assumption)
end
end
