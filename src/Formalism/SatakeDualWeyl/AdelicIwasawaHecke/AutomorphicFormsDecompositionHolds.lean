module

public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

section Rep

variable {G : Type} [Group G] (Γ K : Subgroup G)

theorem mem_AMFK_iff {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    (ρK : Representation k K W) (f : G → W) :
    f ∈ AMFK k Γ K ρK ↔ ∀ γ : Γ, ∀ g : G, ∀ κ : K, f ((γ : G) * g * κ) = ρK κ⁻¹ (f g) := Iff.rfl

theorem exists_rep (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c) (g : G) :
    ∃ p : Γ × K, g = (p.1 : G) * s (DoubleCoset.mk Γ K g) * (p.2 : G) := by
  have h := (@DoubleCoset.eq _ _ Γ K (s (DoubleCoset.mk Γ K g)) g).1 (hs _)
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

variable {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

end Rep

theorem automorphic_forms_level_finite_holds : Formalism.UG.AMFKFinite := by
  intro G _ Γ K k _ _ W _ _ _ ρK hfin
  have hsurj : ∀ c : ClassSet Γ K, ∃ g : G, DoubleCoset.mk Γ K g = c := by
    intro c
    obtain ⟨g, hg⟩ := Quotient.exists_rep c
    exact ⟨g, hg⟩
  let s : ClassSet Γ K → G := fun c => (hsurj c).choose
  have hs : ∀ c, DoubleCoset.mk Γ K (s c) = c := fun c => (hsurj c).choose_spec
  let L : AMFK k Γ K ρK →ₗ[k] (ClassSet Γ K → W) :=
    LinearMap.pi fun c => (LinearMap.proj (s c)).comp (AMFK k Γ K ρK).subtype
  have hinj : Function.Injective L := by
    intro f g hfg
    apply Subtype.ext
    funext x
    obtain ⟨p, hp⟩ := exists_rep Γ K s hs x
    have hf := (mem_AMFK_iff Γ K ρK (f : G → W)).1 f.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hg := (mem_AMFK_iff Γ K ρK (g : G → W)).1 g.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hfc := congrFun hfg (DoubleCoset.mk Γ K x)
    change (f : G → W) (s (DoubleCoset.mk Γ K x)) = (g : G → W) (s (DoubleCoset.mk Γ K x)) at hfc
    rw [← hp] at hf hg
    rw [hf, hg, hfc]
  exact Module.Finite.of_injective L hinj

end Formalism.UG.P
