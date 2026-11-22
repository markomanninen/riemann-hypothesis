module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiedDataReciprocity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKerTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKAtWitnesses
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevExOfOver
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTiedOfLevEx
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Top.Bl
theorem exists_bdRec_of_eq_alt {D D' : D7} {O : Obj D} {O' : Obj D'} (h : (⟨D, O⟩ : Σ D : D7, Obj D) = ⟨D', O'⟩)
    (R : _root_.Formalism.L2.RecTAlt O'.ex) (c : ℝ) :
    ∃ b : _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c, (⟨D, O, b⟩ : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity D O c) = ⟨D', O', R⟩ := by
  cases h
  exact ⟨R, rfl⟩
end GlobalTheory.Mem.Top.Bl
end
