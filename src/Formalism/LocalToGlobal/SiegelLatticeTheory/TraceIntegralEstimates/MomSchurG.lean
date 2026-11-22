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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomSchur
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit

@[expose] public section

set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.Mom

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.CayleySignature

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParamTieG (D : D7) (Cn : ℝ) : Prop :=
  0 < kaS D ∧ ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → IsHCParam lam' →
    ∃ h : ℝ, GapAtLeast (epsSH D.R) lam' h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h

end Formalism.L2.S.Pv.Mom
