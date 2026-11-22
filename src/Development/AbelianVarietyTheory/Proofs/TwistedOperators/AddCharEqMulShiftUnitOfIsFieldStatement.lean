module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharEqMulShiftUnitOfIsField
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CPAsIdeal

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_addChar_eq_mulShift_of_isField : ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ ψ φ : AddChar κf ℂ, ψ ≠ 1 → φ ≠ 1 → ∃ c : κfˣ, ∀ t, φ t = ψ ((c : κf) * t) := by
  first | exact @GlobalTheory.Twist.addChar_eq_mulShift_unit_of_isField | exact GlobalTheory.Twist.addChar_eq_mulShift_unit_of_isField | (intros; apply GlobalTheory.Twist.addChar_eq_mulShift_unit_of_isField <;> assumption)
