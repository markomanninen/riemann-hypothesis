module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsExtendLin

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Flat.HTL

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat

theorem eq_zero_of_forall_om' {A K : Type} [CommRing A] [Field K] [Algebra A K] [CharZero K] {E : Type} [Field E]
    [NumberField E] {c : E ≃+* E} {p R N : ℕ} [Fact p.Prime] {Li : Type} [AddCommGroup Li] [Module K Li]
    (D : HTChart A K c p R N (Module.Dual K Li))
    (hspan : Submodule.span K (D.om : Set (Module.Dual K Li)) = ⊤)
    {e : Li} (he : ∀ w ∈ D.om', w e = 0) : e = 0 := by
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have h1 : ∀ w ∈ D.om, w e = 0 := by
    intro w hw
    have hm : ((p : A) ^ R) • w ∈ D.om' := Submodule.mem_sup_right ⟨w, hw, rfl⟩
    have h := he _ hm
    rw [LinearMap.smul_apply, Algebra.smul_def, map_pow, map_natCast] at h
    exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hp)
  have h2 : Submodule.span K (D.om : Set (Module.Dual K Li)) ≤ LinearMap.ker (Module.Dual.eval K Li e) :=
    Submodule.span_le.2 fun w hw => h1 w hw
  rw [hspan] at h2
  exact (Module.forall_dual_apply_eq_zero_iff K e).1 fun w => h2 (Submodule.mem_top (x := w))

theorem exists_lift_retract : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Li : Type) [AddCommGroup Li] [Module K Li] (D : HTChart A K c p R N (Module.Dual K Li)) (ρ : 𝓞 E →+* Module.End K Li), (∀ (a : 𝓞 E) (w : Module.Dual K Li), D.ρΩ a w = w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) → ∀ (σ : E →+* K) (d : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), algebraMap A K d ≠ 0 → D.ExactMod σ m i → ∃ (J : Li →ₗ[K] (Fin N → K)) (Rr : (Fin N → K) →ₗ[K] Li), (∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ f : Module.Dual A (D.omHT (σ.comp c.toRingHom)), (∀ z : D.omHT (σ.comp c.toRingHom), algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e) ∧ ∀ l, J e l = algebraMap A K (i f l)) ∧ (∀ k, Rr (Pi.single k 1) ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range) ∧ ∀ e ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, ∃ e' ∈ HTL.latOn D (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range, Rr (J e) = e + ((p : K) ^ m) • e' := by
  intro A K _ _ _ _ _ _ _ E _ _ c hc p R N _ Li _ _ D ρ hact σ d m i hd hex
  classical
  have hττ : (σ.comp c.toRingHom).comp c.toRingHom = σ := by
    ext x
    simp [hc]
  have hinj := IsFractionRing.injective A K
  have hE : ∀ e ∈ eigSp ρ σ, ∀ w : Module.Dual K Li, eigProj D.ρΩ (σ.comp c.toRingHom) w e = w e :=
    fun e he w => eigProj_apply D ρ hc hact (σ.comp c.toRingHom) (by rw [hττ]; exact he) w
  have hvec0 : ∀ g : Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∃ e ∈ eigSp ρ σ,
      ∀ z : D.omHT (σ.comp c.toRingHom),
        algebraMap A K d * (z : Module.Dual K Li) e = algebraMap A K (g z) := by
    intro g
    obtain ⟨e, he, hz⟩ := exists_vec D ρ hc hact (σ.comp c.toRingHom) g
    rw [hττ] at he
    refine ⟨(algebraMap A K d)⁻¹ • e, Submodule.smul_mem _ _ he, fun z => ?_⟩
    rw [map_smul, hz, smul_eq_mul, mul_inv_cancel_left₀ hd]
  choose vec hvecS hvec using hvec0
  have hmem : ∀ w ∈ D.om', ∃ z : D.omHT (σ.comp c.toRingHom),
      (z : Module.Dual K Li) = eigProj D.ρΩ (σ.comp c.toRingHom) w :=
    fun w hw => ⟨⟨_, w, hw, rfl⟩, rfl⟩
  let : Module A Li := Module.compHom Li (algebraMap A K)
  have : IsScalarTower A K Li := ⟨fun a k v => by
    change (a • k) • v = algebraMap A K a • (k • v)
    rw [Algebra.smul_def, mul_smul]⟩
  have hsmul : ∀ (a : A) (v : Li), a • v = algebraMap A K a • v := fun _ _ => rfl
  have hvW : ∀ g, vec g ∈ latOn D (eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range := fun g =>
    ⟨hvecS g, fun w hw => by
      obtain ⟨z, hz⟩ := hmem w hw
      rw [← hE _ (hvecS g) w, ← hz, hvec]
      exact ⟨_, rfl⟩⟩
  let Wsub : Submodule A Li :=
    { carrier := latOn D (eigSp ρ σ) (algebraMap A K d) (algebraMap A K).range
      add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun w hw => by
        rw [map_add (f := _), mul_add]
        exact add_mem (ha.2 w hw) (hb.2 w hw)⟩
      zero_mem' := ⟨Submodule.zero_mem _, fun w _ => by
        rw [map_zero, mul_zero]
        exact zero_mem _⟩
      smul_mem' := fun a x hx => ⟨by
          rw [hsmul]
          exact Submodule.smul_mem _ _ hx.1, fun w hw => by
        rw [hsmul, map_smul, smul_eq_mul, mul_left_comm]
        exact mul_mem ⟨a, rfl⟩ (hx.2 w hw)⟩ }
  have hF0 : ∀ (e : Wsub) (z : D.omHT (σ.comp c.toRingHom)), ∃ a : A,
      algebraMap A K a = algebraMap A K d * (z : Module.Dual K Li) e := by
    rintro ⟨e, he⟩ z
    obtain ⟨w, hw, hz⟩ := z.2
    have hz' : eigProj D.ρΩ (σ.comp c.toRingHom) w = (z : Module.Dual K Li) := hz
    change algebraMap A K d * (z : Module.Dual K Li) e ∈ (algebraMap A K).range
    rw [← hz', hE e he.1 w]
    exact he.2 w hw
  choose F hF using hF0
  let eval : Wsub →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)) :=
    { toFun := fun e =>
        { toFun := F e
          map_add' := fun x y => hinj <| by
            rw [map_add, hF, hF, hF, Submodule.coe_add, LinearMap.add_apply, mul_add]
          map_smul' := fun a x => hinj <| by
            rw [RingHom.id_apply, smul_eq_mul, map_mul, hF, hF, Submodule.coe_smul,
              LinearMap.smul_apply, Algebra.smul_def, mul_left_comm] }
      map_add' := fun x y => by
        ext z
        apply hinj
        change algebraMap A K (F (x + y) z) = algebraMap A K (F x z + F y z)
        rw [map_add, hF, hF, hF, Submodule.coe_add, map_add, mul_add]
      map_smul' := fun a x => by
        ext z
        apply hinj
        change algebraMap A K (F (a • x) z) = algebraMap A K (a * F x z)
        rw [map_mul, hF, hF, Submodule.coe_smul, hsmul, map_smul, smul_eq_mul, mul_left_comm] }
  obtain ⟨G, hG⟩ := exists_extend_lin (K := K) Wsub
    (((Algebra.linearMap A K).compLeft (Fin N)) ∘ₗ i ∘ₗ eval)
  obtain ⟨⟨r, hr⟩, -⟩ := hex
  let Rr : (Fin N → K) →ₗ[K] Li := Fintype.linearCombination K fun k => vec (r (Pi.single k 1))
  have hRrS (y : Fin N → K) : Rr y ∈ eigSp ρ σ := by
    simp only [Rr, Fintype.linearCombination_apply]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hvecS _)
  have hRr (y : Fin N → A) (z : D.omHT (σ.comp c.toRingHom)) :
      algebraMap A K d * (z : Module.Dual K Li) (Rr (fun l => algebraMap A K (y l))) =
        algebraMap A K (r y z) := by
    have hy : y = ∑ k, y k • Pi.single k (1 : A) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hy]
    simp only [Rr, Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_left_comm, hvec]
  refine ⟨G, Rr, fun e he => ?_, fun k => ?_, fun e he => ?_⟩
  · exact ⟨eval ⟨e, he⟩, hF _, fun l => congrFun (hG ⟨e, he⟩) l⟩
  · have h1 : Rr (Pi.single k 1) = vec (r (Pi.single k 1)) := by
      simp [Rr, Fintype.linearCombination_apply_single]
    rw [h1]
    exact hvW _
  · let f := eval ⟨e, he⟩
    obtain ⟨w', hw'⟩ := hr f
    have hGe : G e = fun l => algebraMap A K (i f l) := hG ⟨e, he⟩
    let q := (p : K) ^ m
    have hq : q ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    let e' := q⁻¹ • (Rr (G e) - e)
    have he'S : e' ∈ eigSp ρ σ :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (hRrS _) he.1)
    refine ⟨e', ⟨he'S, ?_⟩, ?_⟩
    · intro w hw
      obtain ⟨z, hz⟩ := hmem w hw
      have hzEval : algebraMap A K d * (z : Module.Dual K Li) (Rr (G e) - e) =
          q * algebraMap A K (w' z) := by
        have hf : algebraMap A K (f z) = algebraMap A K d * (z : Module.Dual K Li) e := hF _ _
        rw [map_sub, mul_sub, hGe, hRr, hw', LinearMap.add_apply, LinearMap.smul_apply,
          smul_eq_mul, map_add, map_mul, map_pow, map_natCast, ← hf, add_sub_cancel_left]
      refine ⟨w' z, ?_⟩
      rw [← hE e' he'S w, ← hz]
      change algebraMap A K (w' z) = algebraMap A K d * (z : Module.Dual K Li) (q⁻¹ • (Rr (G e) - e))
      rw [map_smul, smul_eq_mul, mul_left_comm, hzEval, inv_mul_cancel_left₀ hq]
    · change Rr (G e) = e + q • (q⁻¹ • (Rr (G e) - e))
      rw [smul_inv_smul₀ hq]
      abel

end GlobalTheory.CompanionTheory.Ar.Flat.HTL
