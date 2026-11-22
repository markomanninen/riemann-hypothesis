module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HilbertSchmidtNormSubmulInvGeOne
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSchmidt_norm_submul_inv_ge_one : Formalism.FourierDecayAlt.ThreeDimData.NormInv := by
  first | exact @GlobalTheory.BesselNorm.hilbertSchmidt_normInv | exact GlobalTheory.BesselNorm.hilbertSchmidt_normInv | (intros; apply GlobalTheory.BesselNorm.hilbertSchmidt_normInv <;> assumption)
