module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsIncidenceZeroLocus
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def IncIdealNeBotDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)), IsProjPrime Q →
    incIdeal Q k ≠ ⊥ → ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) ≤ ((k : ℕ) : WithBot ℕ∞)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
