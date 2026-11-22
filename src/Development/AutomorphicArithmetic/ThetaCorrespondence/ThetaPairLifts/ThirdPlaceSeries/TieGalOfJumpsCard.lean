module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDescent
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisCompatibilityOfJumps
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DecompAway
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerBisStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisTwistStatement
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TieGalAssembly
theorem tieGal_of_jumpsCard_alt (hDR : GlobalTheory.Published.DeRhamPotSemistable)
    (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (hJ : JumpsCard D.nd D.naut) :
    Formalism.MainNotions.SumRepresentations.At.TieGal D.nd D.naut := by
  refine ⟨GlobalTheory.CrysWD.crysIffWD D, potCrysIffWD D, hJ, fun i => ?_⟩
  exact ⟨_root_.GlobalTheory.WeilDeligne.InertiaSplit.decomp_away_alt hDR hL D P i,
    _root_.GlobalTheory.ConjGal.main_alt_alt hDR hL D P i,
    _root_.GlobalTheory.T.de_rham_weight_direct_sum_alt hDR hL D P i,
    _root_.GlobalTheory.T.de_rham_weight_twist_character_alt hDR hL D P i⟩

theorem main_alt_alt : GlobalTheory.Published.DeRhamPotSemistable →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
      (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
      JumpsCard D.nd D.naut → Formalism.MainNotions.SumRepresentations.At.TieGal D.nd D.naut :=
  fun hDR hL D P hJ => _root_.GlobalTheory.TieGalAssembly.tieGal_of_jumpsCard_alt hDR hL D P hJ
end GlobalTheory.TieGalAssembly
end
