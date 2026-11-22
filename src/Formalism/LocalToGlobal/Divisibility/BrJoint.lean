module

public import Mathlib
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTLower
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas
public import Formalism.GradedWeylDivisibility.FinalC

@[expose] public section

noncomputable section

namespace Formalism.L2.DIV.BrJ

open Formalism.BasicNotions Formalism.MainNotions

theorem branching_interlacing_pairs : PrimeDegreeVariant.Conclusion6 := by
  intro n N h lam sg hI
  exact _root_.gTLower_of Formalism.BasicNotions.factDelDualNabla n N h lam sg hI

variable {D : D7} {u : D.what₂.Word}

variable {D : D7} {u : D.what₂.Word}

end Formalism.L2.DIV.BrJ
