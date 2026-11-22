module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProductStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeriesStatement

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecLaws

section Core

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

abbrev clsOf {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) : IrrGL (k := w.adicCompletion E) :=
  cls (ParLaws.toRep σ)

end Core

end GlobalTheory.RecLaws

namespace GlobalTheory.RecLaws

section Core2

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem rec_hasSatGL (H : IsRec h rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ)
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (clsOf σ)).unr ∧ (rc (clsOf σ)).frobEig = S.map fun z => ((z⁻¹ : ℂˣ) : ℂ) := by
  have hsph : IsSpherical (ParLaws.toRep σ).ρ := by
    have := hS.1
    unfold IsSpherical IsSphericalFor
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact this
  have hu : (rc (clsOf σ)).unr := (ParLaws.unr_iff H _).2 hsph
  obtain ⟨α, hα⟩ := ParLaws.exists_hasSatake_of_unr H hu
  have e : S = Finset.univ.val.map α := hS.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα)
  refine ⟨hu, ?_⟩
  rw [clsOf, ParLaws.rec_eq_diag H hα, WD.frobEig_diag, e, Multiset.map_map]
  rfl

end Core2

end GlobalTheory.RecLaws
