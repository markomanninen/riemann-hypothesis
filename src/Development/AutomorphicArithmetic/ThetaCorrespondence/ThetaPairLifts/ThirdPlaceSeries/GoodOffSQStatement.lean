module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceOutsideBadSets
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffSQ
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_place_not_mem_S_and_Q_of_tieLab :
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
      (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
      (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep),
      _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D →
      Formalism.MainNotions.SumRepresentations.tieLab D →
      ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)),
        GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → w ∉ D.nd.S i ∧ w ∉ D.nd.Q i :=
  _root_.GlobalTheory.OffSQ.good_off_SQ_alt
end
