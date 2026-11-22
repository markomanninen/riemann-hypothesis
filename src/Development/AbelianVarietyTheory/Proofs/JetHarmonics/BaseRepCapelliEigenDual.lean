module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.StatementTBB
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingGapDecayStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstantStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselPeriodAdjointPairStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRegularRepBesselBigCellVectorEqBesselStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselNormSqEqBigCellNormSqStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AemeasurableBesselNormIntegrandBigCellStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFamilyFunctionalsStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilyThroughDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CoefZero


open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal Matrix.Norms.Elementwise in
theorem _root_.GlobalTheory.CoefZero.continuousOn_of_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {m : ℕ∞}
    {f : _root_.Formalism.FourierDecayAlt.B.Mat k r → E} (h : _root_.Formalism.FourierDecayAlt.B.CkOn m (_root_.Formalism.FourierDecayAlt.B.GV k r) f) : ContinuousOn f (_root_.Formalism.FourierDecayAlt.B.GV k r) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfeq⟩ := h g₀ hg₀
  have hc : ContinuousOn f' U := hf'.continuousOn
  have hcont : ContinuousAt f' g₀ := hc.continuousAt (hU.mem_nhds hgU)
  refine hcont.continuousWithinAt.congr_of_eventuallyEq ?_ (hfeq g₀ hgU hg₀)
  filter_upwards [inter_mem_nhdsWithin (_root_.Formalism.FourierDecayAlt.B.GV k r) (hU.mem_nhds hgU)] with g hg
  exact hfeq g hg.2 hg.1

end GlobalTheory.CoefZero
