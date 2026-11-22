module

public import ReciprocityTheory.DualLattices.CotangentSurjective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
public import Development.WeilBound.CoreStatements.HodgeTatePoints.RiRank

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

open PositivityTheory.HtPt.Ri in
theorem rank_one_dual_gauss : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ ψ : AddChar F C, ψ ≠ 1 → ∀ AD : HopfOrder (C := C) R F, AD.carrier = (dualLat AA.carrier).map (fourier (R := R) fun h a : F => ψ (h * a)) → FStable (F := F) AD.carrier ∧ ∀ χ : MulChar F R, χ ≠ 1 → ∀ c cD : R, xIdeal AA.carrier χ = Ideal.span {c} → xIdeal AD.carrier χ = Ideal.span {cD} → v (algebraMap R C c) * v (algebraMap R C cD) = v (∑ a, algebraMap R C (χ⁻¹ a) * ψ a) := by
  intro p _ C _ _ _ v R _ _ hv hpv F _ _ _ _ f hcard AA hM ψ hψ AD hAD
  refine ⟨?_, ?_⟩
  · intro b g hg
    rw [hAD] at hg ⊢
    obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hg
    refine Submodule.mem_map.mpr ⟨fun y => ∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a, ?_, ?_⟩
    · intro f' hf'
      obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R C r = ∑ a, u a * f' (b • a) := hu _ (hM b f' hf')
      refine ⟨r, ?_⟩
      show _ = ∑ y, (∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a) * f' y
      rw [hr, push_sum]
      rfl
    · funext h
      show ∑ y, (∑ a ∈ Finset.univ.filter (fun a => b * a = y), u a) * ψ (h * y) = ∑ a, u a * ψ ((b • h) * a)
      rw [push_sum b u (fun y => ψ (h * y))]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_eq_mul]
      ring_nf
  · intro χ hχ c cD hc hcD
    set G : C := ∑ a, algebraMap R C (χ⁻¹ a) * ψ a with hG
    have hW : ∀ h : F, ∑ a, algebraMap R C (χ⁻¹ a) * ψ (a * h) = algebraMap R C (χ h) * G := by
      intro h
      have e := wsum_eq χ (fun a => ψ a) (wsum_zero_of_ne hv hχ _) h
      simpa [wsum, G] using e
    have hFt : ∀ t : C, fourier (R := R) (fun h a : F => ψ (h * a)) (fun a => t * algebraMap R C (χ⁻¹ a)) = fun h => t * G * algebraMap R C (χ h) := by
      intro t
      funext h
      show ∑ a, t * algebraMap R C (χ⁻¹ a) * ψ (h * a) = _
      calc ∑ a, t * algebraMap R C (χ⁻¹ a) * ψ (h * a) = t * ∑ a, algebraMap R C (χ⁻¹ a) * ψ (a * h) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [mul_comm h a]
            ring
        _ = _ := by rw [hW h]; ring
    have hq : v ((Fintype.card F : C) - 1) = 1 := v_card_sub_one p hv hpv
    have hcm : (fun a => algebraMap R C c * algebraMap R C (χ a)) ∈ AA.carrier :=
      (mem_xIdeal _ _ _).mp (by rw [hc]; exact Ideal.mem_span_singleton_self c)
    have hDm : (fun a => algebraMap R C cD * algebraMap R C (χ a)) ∈ AD.carrier :=
      (mem_xIdeal _ _ _).mp (by rw [hcD]; exact Ideal.mem_span_singleton_self cD)
    have key : ∀ t : C, (∃ s : R, algebraMap R C s = t * algebraMap R C c) →
        v t * v G ≤ v (algebraMap R C cD) := by
      intro t ⟨s, hs⟩
      have hu : (fun a => t * algebraMap R C (χ⁻¹ a)) ∈ dualLat AA.carrier := by
        intro g hg
        have hsum : wsum χ g = ∑ a : F, χ⁻¹ a • fun x => g (a • x) := by
          funext x
          simp [wsum, Finset.sum_apply, Algebra.smul_def]
        have hm : wsum χ g ∈ AA.carrier := by
          rw [hsum]
          exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hM a g hg)
        obtain ⟨r, hr1⟩ := AA.le_int hm 1
        have hr : r ∈ xIdeal AA.carrier χ := by
          apply (mem_xIdeal _ _ _).2
          convert hm using 1
          funext a
          rw [wsum_eq χ g (wsum_zero_of_ne hv hχ g) a, hr1, mul_comm]
        rw [hc] at hr
        obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        refine ⟨k * s, ?_⟩
        have e : ∑ a, t * algebraMap R C (χ⁻¹ a) * g a = t * wsum χ g 1 := by
          simp only [wsum, mul_one, Finset.mul_sum, mul_assoc]
        show _ = ∑ a, t * algebraMap R C (χ⁻¹ a) * g a
        rw [e, ← hr1, map_mul, map_mul, hs]
        ring
      have hm : (fun h => t * G * algebraMap R C (χ h)) ∈ AD.carrier := by
        rw [hAD, ← hFt]
        exact Submodule.mem_map_of_mem hu
      obtain ⟨s', hs'⟩ : ∃ s' : R, algebraMap R C s' = t * G * algebraMap R C (χ 1) := AD.le_int hm 1
      rw [map_one, map_one, mul_one] at hs'
      have hx : s' ∈ xIdeal AD.carrier χ := by
        rw [mem_xIdeal, hs']
        exact hm
      rw [hcD] at hx
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [← map_mul, ← hs', map_mul, map_mul]
      calc v (algebraMap R C k) * v (algebraMap R C cD) ≤ 1 * v (algebraMap R C cD) := by
            gcongr
            exact hv.map_le_one k
        _ = _ := one_mul _
    rw [hAD] at hDm
    obtain ⟨u, hu, hFu⟩ := Submodule.mem_map.mp hDm
    obtain ⟨r, hr⟩ : ∃ r : R, algebraMap R C r = ∑ a, u a * (algebraMap R C c * algebraMap R C (χ a)) := hu _ hcm
    have hinv : ∑ h, algebraMap R C (χ⁻¹ h) * fourier (R := R) (fun h a : F => ψ (h * a)) u h =
        G * ∑ a, u a * algebraMap R C (χ a) := by
      have e1 : ∀ h, fourier (R := R) (fun h a : F => ψ (h * a)) u h = ∑ a, u a * ψ (h * a) := fun h => rfl
      simp_rw [e1, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      calc ∑ h, algebraMap R C (χ⁻¹ h) * (u a * ψ (h * a)) = u a * ∑ h, algebraMap R C (χ⁻¹ h) * ψ (h * a) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun h _ => ?_
            ring
        _ = _ := by rw [hW a]; ring
    have hL : ∑ h, algebraMap R C (χ⁻¹ h) * fourier (R := R) (fun h a : F => ψ (h * a)) u h =
        algebraMap R C cD * ((Fintype.card F : C) - 1) := by
      rw [hFu, ← sum_inv_mul (C := C) χ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    have e2 : ∑ a, u a * (algebraMap R C c * algebraMap R C (χ a)) = algebraMap R C c * ∑ a, u a * algebraMap R C (χ a) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [e2] at hr
    have hmain : G * algebraMap R C r = algebraMap R C c * algebraMap R C cD * ((Fintype.card F : C) - 1) := by
      linear_combination G * hr - algebraMap R C c * hinv + algebraMap R C c * hL
    have hup : v (algebraMap R C c) * v (algebraMap R C cD) ≤ v G := by
      have h2 := congrArg v hmain
      rw [map_mul, map_mul, map_mul, hq, mul_one] at h2
      rw [← h2]
      calc v G * v (algebraMap R C r) ≤ v G * 1 := by
            gcongr
            exact hv.map_le_one r
        _ = v G := mul_one _
    refine le_antisymm hup ?_
    by_cases hc0 : algebraMap R C c = 0
    · have hG0 : G = 0 := by
        by_contra hG0
        have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
        have h3 := key ((p : C) * G)⁻¹ ⟨0, by rw [hc0, mul_zero, map_zero]⟩
        have e3 : ((p : C) * G)⁻¹ * G = (p : C)⁻¹ := by field_simp
        rw [← map_mul, e3, map_inv₀] at h3
        have h4 := h3.trans (hv.map_le_one cD)
        have hvp : v (p : C) ≠ 0 := (Valuation.ne_zero_iff v).mpr hp0
        rw [inv_le_one₀ (pos_iff_ne_zero.mpr hvp)] at h4
        exact absurd hpv (not_lt.mpr h4)
      rw [hG0, hc0]
      simp
    · have h3 := key (algebraMap R C c)⁻¹ ⟨1, by rw [map_one, inv_mul_cancel₀ hc0]⟩
      rw [map_inv₀] at h3
      have hvc : 0 < v (algebraMap R C c) := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff v).mpr hc0)
      rwa [inv_mul_le_iff₀ hvc] at h3

end GlobalTheory.CompanionTheory.Ar.GR
