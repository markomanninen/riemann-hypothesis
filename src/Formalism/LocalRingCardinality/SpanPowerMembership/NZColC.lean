module

public import Formalism.LocalRingCardinality.SpanPowerMembership.ClassRecordRowDimensionZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] (ι : Type) [Fintype ι] [DecidableEq ι]

variable {K ι} (σ : K →+* ℂ)

abbrev FK (ι : Type) : Type := ι → Unit → ℂ

end Std

section Member

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg)

variable (T : ℕ) [hT : Fact T.Prime]

variable (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)

end Member

section Forms

variable {R : Ranks} {Tau : Type} [Fintype Tau] (hc : Tau → HCParam R) (K : ClsPkg) (T : ℕ) [hT : Fact T.Prime]
  (Dst : ℝ) (hD : 0 < Dst) (du : ℕ) (hdu : 0 < du) (Gam : ℝ) (hG : 1 < Gam)
  (Mt : Type) [AddCommGroup Mt] [Module ℂ Mt] (per : FK (K.cls R.m) →ₗ[ℂ] Mt →ₗ[ℂ] ℂ)
  {LL : Type} [Field LL] [NumberField LL] [StarRing LL] (embLL : LL →+* ℂ)
  (Pl : Rows.Places LL) (hTau : Fintype.card Tau = R.f)

end Forms

end Formalism.BasicNotions.Examples₂.NZ
