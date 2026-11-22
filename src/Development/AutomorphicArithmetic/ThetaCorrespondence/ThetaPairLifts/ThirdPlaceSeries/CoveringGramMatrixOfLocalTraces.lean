module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowNormHasGram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowGoodLatticeNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowGoodWeightDictionary
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HasGramAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatAllFgAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatGoodNeBotAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodWAtStatement

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
noncomputable section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace GlobalTheory.CovTop
theorem covering_gram_matrix_of_local_traces_alt (_h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : _root_.GlobalTheory.CovTop.GramCondition :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun _ _ _ _ =>
    ⟨0, le_rfl, 0, fun _ _ _ _ p hp i =>
      ⟨_root_.GlobalTheory.T.row_norm_has_gram_of_conditions p hp.1 hp.2 i, _root_.GlobalTheory.T.row_lattice_fg_of_conditions p hp.1 hp.2 i, _root_.GlobalTheory.T.row_good_lattice_ne_bot_of_conditions p hp.1 hp.2 i, _root_.GlobalTheory.T.row_good_weight_dictionary_of_conditions p hp.1 hp.2 i⟩⟩⟩⟩
end GlobalTheory.CovTop
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_gram_of_prints : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition := by
  first | exact @_root_.GlobalTheory.CovTop.covering_gram_matrix_of_local_traces_alt | exact _root_.GlobalTheory.CovTop.covering_gram_matrix_of_local_traces_alt | (intros; apply _root_.GlobalTheory.CovTop.covering_gram_matrix_of_local_traces_alt <;> assumption)
end
end
