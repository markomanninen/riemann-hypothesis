module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.FlatZetaIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsNormInvSq

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.ThetaInner

def LaurentConst (h : ℂ → ℂ) (s₀ c : ℂ) : Prop :=
  ∃ p : Polynomial ℂ, p.coeff 0 = 0 ∧ Tendsto (fun s => h s - p.eval (s - s₀)⁻¹) (𝓝[≠] s₀) (𝓝 c)


section Interface

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
  [Algebra F E] {A B : Formalism.BasicNotions.HSpace E} (O : RFObj F E A B)


variable {O}

end Interface

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Towers

variable (T : ThetaX D)

end Towers

variable (Z : DivX D) (T : ThetaX D) (X : Formalism.MainNotions.InnerProductFormulaField.Loc D)


end GlobalTheory.ThetaInner

end
