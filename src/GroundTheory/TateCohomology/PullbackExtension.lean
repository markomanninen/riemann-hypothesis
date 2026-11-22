module

public import Mathlib
public import GroundTheory.TateCohomology.AugmentationSES

@[expose] public section

set_option maxSynthPendingDepth 1

open CategoryTheory

namespace GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable (S : ShortComplex (Rep.{u} k G)) {Y : Rep.{u} k G} (β : Y ⟶ S.X₃)

def pullbackSubmodule : Submodule k (S.X₂.V × Y.V) :=
  LinearMap.ker (S.g.hom.toLinearMap ∘ₗ LinearMap.fst k S.X₂.V Y.V -
    β.hom.toLinearMap ∘ₗ LinearMap.snd k S.X₂.V Y.V)

variable {S β} in
theorem mem_pullbackSubmodule {p : S.X₂.V × Y.V} :
    p ∈ pullbackSubmodule S β ↔ S.g.hom p.1 = β.hom p.2 := by
  simp [pullbackSubmodule, sub_eq_zero]

theorem pullbackSubmodule_le_comap (g : G) :
    pullbackSubmodule S β ≤ (pullbackSubmodule S β).comap ((S.X₂.ρ.prod Y.ρ) g) := by
  intro p hp
  rw [Submodule.mem_comap, mem_pullbackSubmodule]
  rw [mem_pullbackSubmodule] at hp
  simp [Rep.hom_comm_apply, hp]

noncomputable abbrev pullbackRep : Rep.{u} k G :=
  Rep.subrepresentation (Rep.of (S.X₂.ρ.prod Y.ρ)) (pullbackSubmodule S β)
    (pullbackSubmodule_le_comap S β)

noncomputable def pullbackFst : pullbackRep S β ⟶ S.X₂ :=
  Rep.ofHom ⟨LinearMap.fst k S.X₂.V Y.V ∘ₗ (pullbackSubmodule S β).subtype, fun _ => rfl⟩

noncomputable def pullbackSnd : pullbackRep S β ⟶ Y :=
  Rep.ofHom ⟨LinearMap.snd k S.X₂.V Y.V ∘ₗ (pullbackSubmodule S β).subtype, fun _ => rfl⟩

theorem g_apply_f_apply (x : S.X₁) : S.g.hom (S.f.hom x) = 0 := by
  change (S.f ≫ S.g).hom x = 0
  rw [S.zero]
  rfl

noncomputable def pullbackιLinear : S.X₁.V →ₗ[k] pullbackSubmodule S β :=
  LinearMap.codRestrict (pullbackSubmodule S β)
    (LinearMap.prod S.f.hom.toLinearMap 0) fun x => by
      rw [mem_pullbackSubmodule]
      simp [g_apply_f_apply]

noncomputable def pullbackι : S.X₁ ⟶ pullbackRep S β :=
  Rep.ofHom ⟨pullbackιLinear S β, fun g => by
    refine LinearMap.ext fun x => Subtype.ext (Prod.ext ?_ ?_)
    · simp [pullbackιLinear, Rep.hom_comm_apply]
    · simp [pullbackιLinear]⟩

theorem pullbackι_pullbackSnd : pullbackι S β ≫ pullbackSnd S β = 0 := by
  ext x
  rfl

noncomputable def pullbackSES : ShortComplex (Rep.{u} k G) :=
  ShortComplex.mk (pullbackι S β) (pullbackSnd S β) (pullbackι_pullbackSnd S β)


variable {S} in
theorem pullbackSES_shortExact (hS : S.ShortExact) : (pullbackSES S β).ShortExact := by
  have hex := function_exact_of_shortExact hS
  have hinj : Function.Injective S.f.hom := (Rep.mono_iff_injective _).1 hS.mono_f
  have hsurj : Function.Surjective S.g.hom := (Rep.epi_iff_surjective _).1 hS.epi_g
  refine shortExact_of_linear ?_ ?_ ?_
  · intro a b hab
    exact hinj (congrArg (fun p : pullbackRep S β => p.1.1) hab)
  · intro y
    obtain ⟨x, hx⟩ := hsurj (β.hom y)
    exact ⟨⟨(x, y), mem_pullbackSubmodule.2 hx⟩, rfl⟩
  · intro p hp
    have hp2 : p.1.2 = 0 := hp
    have hg : S.g.hom p.1.1 = 0 := by
      rw [(mem_pullbackSubmodule.1 p.2), hp2, map_zero]
    obtain ⟨x, hx⟩ := (hex p.1.1).1 hg
    refine ⟨x, Subtype.ext (Prod.ext hx hp2.symm)⟩

end GroundTheory.GroupCoh
