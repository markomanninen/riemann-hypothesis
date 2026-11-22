module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryBlockEmbeddingOntoStabiliser
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryBlockEmbedding_onto_stabiliser : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)), SignCompat e → ∃ j : UpqT P' Q' →* UpqT P Q, IsBlockEmb e j ∧ Topology.IsClosedEmbedding j ∧ Set.range j = {g | act g (baseVec e) = baseVec e} := by
  first | exact @GlobalTheory.BlockEmbedding.exists_blockEmb | exact GlobalTheory.BlockEmbedding.exists_blockEmb | (intros; apply GlobalTheory.BlockEmbedding.exists_blockEmb <;> assumption)
