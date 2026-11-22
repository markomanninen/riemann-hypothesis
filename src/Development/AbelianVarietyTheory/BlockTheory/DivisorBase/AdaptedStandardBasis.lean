module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.SharpRestriction.ElevenLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

def IsThetaWt (la : Weight Dw) (n : ℕ) : Prop :=
  8 ∣ n ∧ (∀ τ, Antitone (la τ)) ∧
    (∀ τ (i : Fin (Dw.p + Dw.q)), (i : ℕ) < Dw.p → ((n / 2 : ℕ) : ℤ) ≤ la τ i) ∧
    (∀ τ (i : Fin (Dw.p + Dw.q)), Dw.p ≤ (i : ℕ) → la τ i ≤ -((n / 2 : ℕ) : ℤ)) ∧
    ∀ τ (i k : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (k : ℕ) = Dw.p → (n : ℤ) + 2 < la τ i - la τ k

end Weights

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

variable (Xo : Moduli Dw l) (c : Coeff l)

def polyNorm {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : ℝ :=
  Real.sqrt (∑ s : c.F →+* ℂ, ∑ m ∈ P.support, ‖s (P.coeff m)‖ ^ 2)



variable {Xo c} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

end Family

section Constants

variable (D : D7) (large₂ : SizeData₂ D)

end Constants

section Statement

variable (D : D7) (large₂ : SizeData₂ D)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData
