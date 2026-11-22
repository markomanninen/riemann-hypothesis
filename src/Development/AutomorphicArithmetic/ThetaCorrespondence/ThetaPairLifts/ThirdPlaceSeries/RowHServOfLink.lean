module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BuiltCHasPart
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BundleBothPartsOfStandardKernelOfGlobalArtinReciStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColumnChoiceWithTies
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CountsIrreducibilityConstants
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ServHRowLinkRStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowHServOfKerServ
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory
theorem row_hServ_of_link_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition),
    (∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c), Lk K β c b → _root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p K β c b.R) →
    _root_.GlobalTheory.Fc.R1.SlotServiceCondition (IsGoodE p.s) Lk := by
  intro hA hL p Lk hLk
  have h1 := Row.map (Bd := _root_.GlobalTheory.Fc.BundleCondition) (Q := IsGoodE p.s) (Lk := Lk) (Bd' := _root_.GlobalTheory.Mem.Top.Bl.BoundaryReciprocity) (Q' := IsGoodE p.s) (Lk' := _root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p)
    (fun _ _ _ b => b.R) (fun _ _ _ _ _ h => h) (fun K β c b _ h => hLk K β c b h) (_root_.GlobalTheory.T.reciprocity_kernel_of_artin hA p)
  exact _root_.GlobalTheory.Fc.R1.row_hServ_of_kerServ_alt _ Lk h1
end GlobalTheory
end
