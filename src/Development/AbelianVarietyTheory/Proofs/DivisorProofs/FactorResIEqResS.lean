module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TameInvariantLevelAction
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GeoActCompare

open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct

section Res

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def resI (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) : Formalism.L2.Herm.intAf F E →+* 𝓞 E ⧸ I :=
  ((RingEquiv.ofBijective (cmpS F I) (cmpS_bij (F := F) I hI)).symm : _ →+* 𝓞 E ⧸ I).comp
    (Ideal.Quotient.mk (idS F I))

variable {F}

theorem resI_oToS (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (a : 𝓞 E) :
    resI F I hI (oToS F E a) = Ideal.Quotient.mk I a := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _
  rw [RingEquiv.symm_apply_eq]
  rfl

theorem resI_eq_zero_iff (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) (s : Formalism.L2.Herm.intAf F E) :
    resI F I hI s = 0 ↔ s ∈ idS F I := by
  unfold resI
  rw [RingHom.comp_apply]
  show (RingEquiv.ofBijective (cmpS F I) _).symm _ = _ ↔ _
  rw [map_eq_zero_iff _ (RingEquiv.injective _), Ideal.Quotient.eq_zero_iff_mem]

theorem resS_eq_resI (w : Pl E) : resS F w = resI F w.asIdeal w.ne_bot := rfl

end Res

section CRT

variable {E : Type} [Field E] [NumberField E] {I : Ideal (𝓞 E)} {Pg : Finset (Pl E)}

end CRT

end GlobalTheory.GeoActCompare
