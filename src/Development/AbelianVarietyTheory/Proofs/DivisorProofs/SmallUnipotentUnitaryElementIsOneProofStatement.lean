module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnipotentUnitaryElementIsOneProof
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.SmallElementStatement E := by
  first | exact @GlobalTheory.SmallElement.smallElement | exact GlobalTheory.SmallElement.smallElement | (intros; apply GlobalTheory.SmallElement.smallElement <;> assumption)
