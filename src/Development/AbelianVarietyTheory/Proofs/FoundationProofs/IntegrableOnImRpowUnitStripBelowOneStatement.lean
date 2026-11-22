module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowUnitStripBelowOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralEqIteratedStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumParsevalQExpansionHorizontalLineStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement

@[expose] public section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_im_rpow_unitStrip_below_one : ∀ (s : ℝ), 0 < s → IntegrableOn (fun τ : ℍ => τ.im ^ (s + 1)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  first | exact @GlobalTheory.EisM.stripLow_integrableOn_im_rpow | exact GlobalTheory.EisM.stripLow_integrableOn_im_rpow | (intros; apply GlobalTheory.EisM.stripLow_integrableOn_im_rpow <;> assumption)
