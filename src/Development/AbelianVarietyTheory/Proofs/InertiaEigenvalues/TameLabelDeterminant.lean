module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjGenTransportExists
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitaryStatement
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugatePlacesCompletion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjSelfDualHeckeCharConjugatePlaceComponentInvStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LabConjPlace

open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL

theorem loc_artin_ine {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) (χ : HChar E) (hu : χ.UnrAt w)
    (σ : Weil h) (hσ : (σ : G E Ω) ∈ Ine (F := E) A) : χ.loc w (a σ) = 1 := by
  have h1 := ha.ord_eq σ
  rw [deg_eq_zero_iff.2 hσ, neg_zero, SphCompletion.ord_completion, neg_eq_zero] at h1
  have h0 : Valued.v ((a σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0 := by simp
  apply hu
  show Valued.v _ = 1
  rw [← WithZero.exp_log h0, h1, WithZero.exp_zero]

end GlobalTheory.LabConjPlace

