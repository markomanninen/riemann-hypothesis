module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsPassToMovedDivisionLatticesHeightsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeptChoiceUpperLattice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralStageDataTransferLatticesHeightsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionGeometryScalarsTransferSetDivisionStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.HeightCounting.Up

set_option maxHeartbeats 4000000

theorem kept_trans {D D' D'' : D7} {c : NChoice D} {c' : NChoice D'} {c'' : NChoice D''}
    (h : Kept c c') (h' : Kept c' c'') : Kept c c'' := by
  obtain ⟨g1, s1, f1, b1, t1, d1, q1, k1, p1⟩ := h
  obtain ⟨g2, s2, f2, b2, t2, d2, q2, k2, p2⟩ := h'
  refine ⟨?_, ?_, ?_, b1.trans b2, t1.trans t2, d1.trans d2, q1.trans q2, k1.trans k2, p1.trans p2⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := g1
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := g2
    exact ⟨a1.trans e1, a2.trans e2, a3.trans e3, a4.trans e4, a5.trans e5, a6.trans e6, a7.trans e7, a8.trans e8⟩
  · cases s1; cases s2; constructor <;> (apply HEq.trans <;> assumption)
  · cases f1; cases f2; constructor <;> (apply HEq.trans <;> assumption)

end GlobalTheory.HeightCounting.Up

end
