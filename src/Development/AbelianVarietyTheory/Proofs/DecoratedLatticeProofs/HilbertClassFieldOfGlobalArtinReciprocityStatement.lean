module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
public import ReciprocityTheory.NeutralLocalFields.HilbertClassField
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertClassField_of_globalArtinReciprocity : GlobalTheory.Published.GlobalArtinReciprocity → Neutral.HilbertClassField.Statement := by
  first | exact @GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField | exact GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField | (intros; apply GlobalTheory.Published.GlobalArtinReciprocity.hilbertClassField <;> assumption)
