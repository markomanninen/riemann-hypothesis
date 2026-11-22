module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentification
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    GlobalTheory.RowTie.WDTie N A →
      GlobalTheory.ThetaExh.ParamLaws N A ∧ GlobalTheory.RowTie.CharLaws N A ∧
        GlobalTheory.RowTie.Cancel N A :=
  GlobalTheory.RowLaws.main
