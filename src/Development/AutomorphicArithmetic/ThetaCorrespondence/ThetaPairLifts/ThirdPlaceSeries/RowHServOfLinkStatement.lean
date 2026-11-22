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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowHServOfLink
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hServ_of_linkR : GlobalTheory.Published.GlobalArtinReciprocity → ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Lk : LkT _root_.GlobalTheory.Fc.BundleCondition), (∀ (K : Ctx) (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c), Lk K β c b → _root_.GlobalTheory.Mem.Top.Bl.ReciprocityLinkage p K β c b.R) → _root_.GlobalTheory.Fc.R1.SlotServiceCondition (IsGoodE p.s) Lk := by
  first | exact @_root_.GlobalTheory.row_hServ_of_link_alt | exact _root_.GlobalTheory.row_hServ_of_link_alt | (intros; apply _root_.GlobalTheory.row_hServ_of_link_alt <;> assumption)
end
