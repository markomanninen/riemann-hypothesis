module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CgEqOfChar
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_rep_one_eq_of_character_choice : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (π : D.naut.CG 1), haveI := GlobalTheory.CuspRep.host_isCMField D.host; ((P.cg.e 1 π).1 : GlobalTheory.CuspRep.CG D.host.E 1) = GlobalTheory.CuspRep.CG.ofChar (P.chr.e1 π).1 := by
  first | exact @_root_.GlobalTheory.RankOneChar.cg_eq_ofChar_alt | exact _root_.GlobalTheory.RankOneChar.cg_eq_ofChar_alt | (intros; apply _root_.GlobalTheory.RankOneChar.cg_eq_ofChar_alt <;> assumption)
end
