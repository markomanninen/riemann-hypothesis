module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem latC_full_lattice : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), ∃ L : Submodule (𝓞 E) (Fin W.rank → E), (L : Set (Fin W.rank → E)) = latC W ∧ L.FG ∧ Submodule.span E (L : Set (Fin W.rank → E)) = ⊤ := by
  intro E _ _ _ W
  refine ⟨W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E)), ?_, W.standardTuple_isLattice.fg.map _, ?_⟩
  · ext x
    simp only [latC, SetLike.mem_coe, Submodule.mem_map, Set.mem_ofPred_eq]
    rw [← W.frame.equivFun_symm_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨_, h, W.frame.equivFun.apply_symm_apply x⟩
  · have h : Submodule.span E (W.L0 : Set W.V) = ⊤ := by
      let U := Submodule.span E (W.L0 : Set W.V)
      change U = ⊤
      by_contra h
      let e : W.V ≃ₗ⋆[E] W.V :=
        (W.frame.equivFun.trans (starLinearEquiv E)).trans W.frame.equivFun.symm
      let g : W.V →ₗ[E] Module.Dual E U :=
        (LinearMap.domRestrict' U).comp (W.hT.comp e.toLinearMap)
      have hdim : Module.finrank E (Module.Dual E U) < Module.finrank E W.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨z, hz, hz₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : E) : a • e z ∈ W.L0 := by
        rw [← W.baseLattice_isUnimodular]
        simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
          Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
        intro y hy
        have hzy : W.hT (e z) y = 0 :=
          congrArg (fun f : Module.Dual E U => f ⟨y, Submodule.subset_span hy⟩)
            (LinearMap.mem_ker.mp hz)
        have hyz : W.hT y (e z) = 0 := by
          have hh := W.herm.eq (e z) y
          simpa [hzy] using hh.symm
        simp [hyz]
      let i : E →ₗ[𝓞 E] W.L0 :=
        ((LinearMap.toSpanSingleton E _ (e z)).restrictScalars (𝓞 E)).codRestrict W.L0 hsmul
      let : Module.Finite (𝓞 E) W.L0 := Module.Finite.iff_fg.mpr W.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField E
        (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
    have : ((W.L0.map (W.frame.equivFun.toLinearMap.restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin W.rank → E)) :
        Set (Fin W.rank → E)) = W.frame.equivFun.toLinearMap '' (W.L0 : Set W.V) := rfl
    rw [this, ← Submodule.map_span, h, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.Mem.Vol
