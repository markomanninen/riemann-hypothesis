module

public import Mathlib
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.ConjugateSelfDual.Statement
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG Polynomial
open scoped TensorProduct

namespace GlobalTheory.SphPar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def HasDiv {n : ℕ} (O : Subring L) (d : List ℤ) (g : GL (Fin n) L) : Prop :=
  ∃ ϖ : L, Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ∧
    ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O,
      (g : Matrix (Fin n) (Fin n) L) =
        (a : Matrix (Fin n) (Fin n) L) * Matrix.diagonal (fun i : Fin n => ϖ ^ d.getD i 0) * (b : Matrix (Fin n) (Fin n) L)

def divInd {n : ℕ} (O : Subring L) (d : List ℤ) : GL (Fin n) L → ℂ := Set.indicator {g | HasDiv O d g} 1

end Local

section Global

variable {E : Type} [Field E] [NumberField E]

variable [StarRing E]

end Global

variable {D : D7}

end GlobalTheory.SphPar

end
