module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import GroundTheory.LocalFields.MainTheorem
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

namespace GlobalTheory.CompanionTheory.LocRes

theorem natCard_residueField_eq_normV : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)), Nat.card 𝓀[v.adicCompletion F] = normV v := by
  intro F _ _ v
  rw [GroundTheory.Global.natCard_residueField_adicCompletion v, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  rfl

end GlobalTheory.CompanionTheory.LocRes
