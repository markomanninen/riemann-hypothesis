module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.BaseChange

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL.ResDeg

theorem normV_eq_under_pow : ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (w : HeightOneSpectrum (𝓞 M)), ∃ f : ℕ, normV w = normV (w.under (𝓞 K)) ^ f := by
  intro K M _ _ _ _ _ w
  refine ⟨w.asIdeal.inertiaDeg (𝓞 K), ?_⟩
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 M) w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

end GlobalTheory.AboveL.ResDeg
