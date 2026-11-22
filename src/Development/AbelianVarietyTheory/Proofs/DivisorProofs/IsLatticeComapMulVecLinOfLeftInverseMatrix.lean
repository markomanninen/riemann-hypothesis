module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

theorem isLattice_comap_mulVecLin_of_leftInverse (E : Type) [Field E] [NumberField E] (n n₁ : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (ι : Matrix (Fin n) (Fin n₁) E)
    (P : Matrix (Fin n₁) (Fin n) E) (hPι : P * ι = 1) (hL : L.IsFullLattice E) :
    (L.comap ((Matrix.mulVecLin ι).restrictScalars (𝓞 E))).IsLattice E := by
  set f : (Fin n₁ → E) →ₗ[𝓞 E] (Fin n → E) := (Matrix.mulVecLin ι).restrictScalars (𝓞 E) with hf
  set g : (Fin n → E) →ₗ[𝓞 E] (Fin n₁ → E) := (Matrix.mulVecLin P).restrictScalars (𝓞 E) with hg
  have hgf : ∀ u, g (f u) = u := by
    intro u
    simp [hf, hg, Matrix.mulVec_mulVec, hPι]
  apply Submodule.IsLattice.of_fg E
  have hN : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian L hL.fg
  have h1 : ((L.comap f).map f).FG :=
    isNoetherian_submodule.1 hN _ (Submodule.map_comap_le f L)
  have h2 : ((L.comap f).map f).map g = L.comap f := by
    rw [← Submodule.map_comp]
    ext u
    simp only [Submodule.mem_map, LinearMap.coe_comp, Function.comp_apply, hgf]
    exact ⟨fun ⟨v, hv, he⟩ => he ▸ hv, fun hu => ⟨u, hu, rfl⟩⟩
  rw [← h2]
  exact h1.map g

end GlobalTheory
