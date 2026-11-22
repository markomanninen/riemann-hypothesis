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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiedDataReciprocity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKerTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKAtWitnesses
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevExOfOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTiedOfLevEx
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRecPinEStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsBdRecOfEq
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
namespace GlobalTheory.Mem.Top.Bl
theorem exists_linked_of_eq_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
    (hB : ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ)
      (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}),
      q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b))
    (q : WPt p.s K) (R' : _root_.Formalism.L2.RecTAlt q.O.ex) (hR' : _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R') (c : ℝ) {D : D7} {O : Obj D} (R : _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c)
    (he : (⟨D, O, R⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c) = ⟨q.w.D q.Z, q.O, R'⟩) (hsc : O.L.sc = K.s)
    (hv : Val K.C K.cD K.ch O.L) (n : {n : ℕ × ℕ // D.s.Del = (n.1 : ℚ) ∧ O.L.etaSz = (D.R.m : ℝ) * (n.2 : ℝ)}) :
    ∃ b : _root_.GlobalTheory.Fc.BundleCondition D O c, ∃ (q' : WPt p.s K) (b' : _root_.GlobalTheory.Fc.BundleCondition (q'.w.D q'.Z) q'.O c), Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q' b') ∧
      (⟨D, O, b⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c) = ⟨q'.w.D q'.Z, q'.O, b'⟩ := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp he
  obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  obtain ⟨b, -, hW⟩ := hB q R' hR' c n hsc hv
  exact ⟨b, q, b, hW, rfl⟩
theorem exBL_isLinked_alt : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), WitExE p.s → (GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z)) → (GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (c : ℝ) (_ : {n : ℕ × ℕ // (q.w.D q.Z).s.Del = (n.1 : ℚ) ∧ q.O.L.etaSz = ((q.w.D q.Z).R.m : ℝ) * (n.2 : ℝ)}), q.O.L.sc = K.s → Val K.C K.cD K.ch q.O.L → ∃ b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c, b.R = R ∧ Nonempty (_root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b)) → GlobalTheory.Fc.ExBL KPx (IsBuiltE p.s) (IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) := by
  intro hA hW hRay hL p hWit hZe hB
  refine ⟨fun _ _ _ _ _ => True, GlobalTheory.Fc.largeBaseProperty_true, ?_⟩
  unfold GlobalTheory.Fc.ExB
  refine GlobalTheory.Fc.EvP.mono (fun κ K _ H => ?_) (GlobalTheory.Fc.EvP.and hZe hB)
  intro β hβ c
  obtain ⟨q, hq, hE⟩ := hWit K β hβ.1
  obtain ⟨C5, c6, Cb, hG⟩ := β.good
  have hO : Over β.X.toD7 K.P K.Lv := by
    obtain ⟨sp, hT, hY, hA', hV, hz, e, -⟩ := β.c.isOver
    exact ⟨sp, hT, hY, hA', hV, hz, β.X, e, rfl⟩
  have hP : K.P.H.levelPrimes = {K.P.H.g 0, K.P.H.g 1, K.P.H.pde, K.P.H.pde', DC.q0H K.P.H} :=
    hG.host.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hLT : Formalism.L2.Host.LevelTied β.D :=
    GlobalTheory.Mem.HD.levelTied_of_levEx _ ((GlobalTheory.Mem.HD.levEx_of_over _ _ _ hO hP).2 _ _)
  have hD : β.D = q.w.D q.Z := congrArg Sigma.fst hq
  have hLT' : Formalism.L2.Host.LevelTied (q.w.D q.Z) := hD ▸ hLT
  obtain ⟨R', hR'⟩ := _root_.GlobalTheory.T.exists_reciprocity_record_compatible hA hW hRay hL p K q hLT' (H.1 q) hE
  obtain ⟨R, he⟩ := _root_.GlobalTheory.Mem.Top.Bl.exists_bdRec_of_eq_alt hq R' c
  have hv : Val K.C K.cD K.ch β.O.L := β.p.pt_val β.val
  exact _root_.GlobalTheory.Mem.Top.Bl.exists_linked_of_eq_alt H.2 q R' hR' c R he β.sc hv ⟨(_, _), hv.Del_eq, hv.eta_eq⟩
end GlobalTheory.Mem.Top.Bl
end
