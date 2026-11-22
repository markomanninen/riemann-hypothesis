module

public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfProductFormula
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.CellDef

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocalSplitGroups Formalism.MainNotions.JointEigenvalueBoundsFromAnyDatum Formalism.MainNotions.LocalModelPeriodLattices
open scoped nonZeroDivisors

section Blocks

variable {A B : Type} [Monoid B] (f : ℕ → ℕ → A → B)

end Blocks

section Van

variable {D : Formalism.BasicNotions.D7}

end Van

section Top

variable {D : Formalism.BasicNotions.D7}

end Top

section Red2

open scoped ComplexOrder
open Formalism.MainNotions

variable {D : Formalism.BasicNotions.D7}

variable {eps : ℝ} (Fm : FamP eps) {Y : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i)}

end Red2

end Formalism.MainNotions.BridgeLemma

end
