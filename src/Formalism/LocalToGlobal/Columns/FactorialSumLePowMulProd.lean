module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.BrzoPairAtZeroRight
public import Formalism.LocalToGlobal.Columns.BrzColLatOneLattice
public import Formalism.LocalToGlobal.Columns.SliceIntegralDeltaNeBot

@[expose] public section

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.HermitianLattices.TraceIntegrality

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

def extQ (lam : DomWeight n) : ℚ := Formalism.GradedWeylDivisibility.fockQ (extremal ℚ n lam) (extremal ℚ n lam)

end Std

section Std2

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

end Std2

section Deg

variable (K : Type) [Field K] [NumberField K] [StarRing K] {n : ℕ} (lam : DomWeight n)

end Deg

end Formalism.L2.Col
