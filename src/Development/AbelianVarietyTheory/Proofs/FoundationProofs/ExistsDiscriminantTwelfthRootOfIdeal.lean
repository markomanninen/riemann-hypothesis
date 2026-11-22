module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedOfContract
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel

@[expose] public section

noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

namespace GlobalTheory.Glob.IntegralWittCoefficients

theorem isCurveIdeal_top (D : D7) : IsCurveIdeal D ⊤ :=
  ⟨top_ne_bot, by simp⟩

end GlobalTheory.Glob.IntegralWittCoefficients
