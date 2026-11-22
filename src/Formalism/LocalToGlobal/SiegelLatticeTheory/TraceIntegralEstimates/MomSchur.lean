module

public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.OrderedAtRanksOfPositionElement
public import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotSetU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuotientInvariantMeasurability.MeasurableAvgS
public import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotInv
public import Formalism.PeriodIntegrals.QuotSetU
public import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
public import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.BesselNVGClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible

@[expose] public section

set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.Mom

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.CayleySignature

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem psiGen_const {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    psiGen k r z (fun _ => c) = psi k r z c := by
  funext g
  unfold psiGen psi ell ellA
  rw [Finset.mul_sum]




end Formalism.L2.S.Pv.Mom
