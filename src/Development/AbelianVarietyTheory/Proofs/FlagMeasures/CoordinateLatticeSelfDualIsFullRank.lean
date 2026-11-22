module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St.G

theorem coordLat_isLat (D : D7) (X : HidaSetting D) :
    IsLat ((VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E))) := by
  have hcomb : ∀ x : Fin _ → D.host.E,
      Fintype.linearCombination D.host.E X.bas x = X.bas.equivFun.symm x := by
    intro x
    rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply]
  have heq : (VS D).L0.comap ((Fintype.linearCombination D.host.E X.bas).restrictScalars (𝓞 D.host.E)) =
      (VS D).L0.map (X.bas.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap := by
    ext x
    simp only [Submodule.mem_comap, LinearMap.restrictScalars_apply, hcomb, Submodule.mem_map,
      LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply]
    constructor
    · intro hx
      exact ⟨_, hx, X.bas.equivFun.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  rw [heq]
  refine ⟨Module.Finite.iff_fg.2 ((VS D).standardTuple_isLattice.fg.map _), ?_⟩
  have : ((VS D).L0.map (X.bas.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap : Set (Fin _ → D.host.E)) =
      X.bas.equivFun.toLinearMap '' ((VS D).L0 : Set (VS D).V) := rfl
  have hspan : Submodule.span D.host.E ((VS D).L0 : Set (VS D).V) = ⊤ := by
    let V := VS D
    let W := Submodule.span D.host.E (V.L0 : Set V.V)
    change W = ⊤
    by_contra h
    let e : V.V ≃ₗ⋆[D.host.E] V.V :=
      (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
    let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
      (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
    have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) <
        Module.finrank D.host.E V.V := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨z, hz, hz₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : D.host.E) : a • e z ∈ V.L0 := by
      rw [← V.baseLattice_isUnimodular]
      simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual,
        Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
      intro y hy
      have hzy : V.hT (e z) y = 0 :=
        congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩)
          (LinearMap.mem_ker.mp hz)
      have hyz : V.hT y (e z) = 0 := by
        have hh := V.herm.eq (e z) y
        simpa [hzy] using hh.symm
      simp [hyz]
    let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
      ((LinearMap.toSpanSingleton D.host.E _ (e z)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
    let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
    let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective D.host.E (fun hzero => hz₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField D.host.E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 D.host.E) D.host.E) (Field.toIsField D.host.E))
  rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.St.G
