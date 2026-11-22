module

public import Mathlib

@[expose] public section

namespace UpperTheory.Reformulated.B.TwistedKernelFixed

noncomputable def IsSmooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] (ρ : Representation k G V) : Prop :=
  ∀ v : V, IsOpen {g : G | ρ g v = v}

theorem aux2 {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) {a b : V}
    (ha : a ∈ {v : V | ∀ h : H, ρ h v = (χ h : k) • v})
    (hb : b ∈ {v : V | ∀ h : H, ρ h v = (χ h : k) • v}) (h : H) :
    ρ h (a + b) = (χ h : k) • (a + b) := by
  rw [map_add (f := _), ha h, hb h, smul_add]

theorem aux3 {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) (h : H) :
    ρ h (0 : V) = (χ h : k) • (0 : V) := by
  rw [map_zero, smul_zero]

theorem aux4 {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) (c : k) {v : V}
    (hv : v ∈ {v : V | ∀ h : H, ρ h v = (χ h : k) • v}) (h : H) :
    ρ h (c • v) = (χ h : k) • c • v := by
  rw [map_smul, hv h, smul_comm]

noncomputable def eig {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) (χ : H →* kˣ) : Submodule k V where
  carrier := {v : V | ∀ h : H, ρ h v = (χ h : k) • v}
  add_mem' := @aux2 k G V _ _ _ _ ρ H χ
  zero_mem' := aux3 ρ H χ
  smul_mem' := aux4 ρ H χ

noncomputable def fixed {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (H : Subgroup G) : Submodule k V :=
  eig ρ H 1

noncomputable def twKer {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Submodule k V :=
  Submodule.span k {w : V | ∃ (n : N) (v : V), w = ρ n v - (ψ n : k) • v}

private theorem sum_shift {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : H →* (V →ₗ[ℂ] V)) (K : Subgroup H) [K.Normal] [Fintype (H ⧸ K)] (u : V)
    (hu : ∀ k ∈ K, ρ k u = u) (n : H) :
    ∑ q : H ⧸ K, ρ q.out (ρ n u) = ∑ q : H ⧸ K, ρ q.out u := by
  refine Fintype.sum_equiv (Equiv.mulRight (n : H ⧸ K)) _ _ fun q => ?_
  have h1 : ((q.out * n : H) : H ⧸ K) = (((q * (n : H ⧸ K)).out : H) : H ⧸ K) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
  have h2 := hu _ (QuotientGroup.eq.mp h1)
  have h3 : (q * (n : H ⧸ K)).out = q.out * n * ((q.out * n)⁻¹ * (q * (n : H ⧸ K)).out) := by
    rw [mul_inv_cancel_left]
  rw [Equiv.coe_mulRight, h3, map_mul, Module.End.mul_apply, h2, map_mul, Module.End.mul_apply]

theorem eq_zero_of_fixed {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ G V} [TopologicalSpace G] [IsTopologicalGroup G] (hs : IsSmooth π)
    {H : Subgroup G} (hH : IsCompact (H : Set G)) {v : V} (hv : v ∈ fixed π H)
    (hw : v ∈ twKer π H (1 : H →* ℂˣ)) : v = 0 := by
  classical
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH
  have key : ∀ w ∈ twKer π H (1 : H →* ℂˣ),
      ∃ K : Subgroup H, K.FiniteIndex ∧ ∀ (L : Subgroup H) [L.Normal] [Fintype (H ⧸ L)], L ≤ K →
        ∑ q : H ⧸ L, π (q.out : H) w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨n, u, rfl⟩ := hx
      let K : Subgroup H :=
        { carrier := {h | π (h : G) u = u}
          mul_mem' := fun {a b} ha hb => by
            have ha' : π (a : G) u = u := ha
            have hb' : π (b : G) u = u := hb
            show π ((a : G) * b) u = u
            rw [map_mul, Module.End.mul_apply, hb', ha']
          one_mem' := by
            show π (1 : G) u = u
            rw [map_one, Module.End.one_apply]
          inv_mem' := fun {a} ha => by
            have ha' : π (a : G) u = u := ha
            show π ((a : G)⁻¹) u = u
            conv_lhs => rw [← ha']
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
      have hK : IsOpen (K : Set H) := (hs u).preimage continuous_subtype_val
      have := Subgroup.quotient_finite_of_isOpen K hK
      refine ⟨K, Subgroup.finiteIndex_of_finite_quotient, fun L _ _ hL => ?_⟩
      have := sum_shift (π.comp H.subtype) L u (fun k hk => hL hk) n
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr this
    | zero => exact ⟨⊤, inferInstance, fun L _ _ _ => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨K₁, h₁, hx⟩ := hx
      obtain ⟨K₂, h₂, hy⟩ := hy
      refine ⟨K₁ ⊓ K₂, inferInstance, fun L _ _ hL => ?_⟩
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [hx L (hL.trans inf_le_left), hy L (hL.trans inf_le_right), add_zero]
    | smul c x _ hx =>
      obtain ⟨K, h, hx⟩ := hx
      refine ⟨K, h, fun L _ _ hL => ?_⟩
      simp only [map_smul]
      rw [← Finset.smul_sum, hx L hL, smul_zero]
  obtain ⟨K, hK, h⟩ := key v hw
  have : Fintype (H ⧸ K.normalCore) := Fintype.ofFinite _
  have h0 := h K.normalCore K.normalCore_le
  have hv' : ∀ g : H, π (g : G) v = v := fun g => by
    have := hv g
    simpa using this
  simp only [hv', Finset.sum_const, Finset.card_univ] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h0
  exact (smul_eq_zero.mp h0).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end UpperTheory.Reformulated.B.TwistedKernelFixed
