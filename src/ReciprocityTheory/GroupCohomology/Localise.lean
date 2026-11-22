module

public import ReciprocityTheory.GroupCohomology.LocaliseA

@[expose] public section

namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function

universe u

theorem localise_holds : LocaliseStatement.{u} := by
  intro R _ G _ _ _ _ t L V j hφ hu he hcov n
  obtain ⟨e, he⟩ := he
  have localiseCx {A B : Cx R} (f : Hom A B) (hj : ∀ k, Injective (f.f k))
      (ht : ∀ k, Bijective fun x : B.X k => t • x)
      (hc : ∀ k (x : B.X k), ∃ (m : ℕ) (y : A.X k), f.f k y = t ^ m • x)
      (k : ℕ) : IsLocalizedModule (Submonoid.powers t) (f.H k) := by
    constructor
    · rintro ⟨_, m, rfl⟩
      show IsUnit (algebraMap R (Module.End R (B.H k)) (t ^ m))
      rw [map_pow]
      exact ((Module.End.isUnit_iff _).2 (bij_H_of_bij t ht k)).pow m
    · intro y
      induction y using H_ind with
      | h x hx =>
        obtain ⟨m, a, ha⟩ := hc k x
        have ha0 : A.d k a = 0 := (hj (k + 1)) (by
          rw [f.comm, ha, cx_smul_d, hx, smul_zero, map_zero])
        refine ⟨(A.cls k a ha0, ⟨t ^ m, m, rfl⟩), ?_⟩
        show (t ^ m) • B.cls k x hx = f.H k (A.cls k a ha0)
        rw [cls_smul, Hom.H_cls]
        exact cls_congr _ _ ha.symm
    · have key : ∀ z : A.H k, f.H k z = 0 → ∃ c : Submonoid.powers t, c • z = 0 := by
        intro z hz
        induction z using H_ind with
        | h g hg =>
          rw [Hom.H_cls, cls_eq_zero_iff] at hz
          cases k with
          | zero =>
            have h0 : f.f 0 g = 0 := hz
            refine ⟨1, ?_⟩
            rw [one_smul, cls_eq_zero_iff]
            exact (hj 0) (h0.trans (map_zero _).symm)
          | succ k =>
            obtain ⟨h, hh⟩ := hz
            obtain ⟨m, a, ha⟩ := hc k h
            refine ⟨⟨t ^ m, m, rfl⟩, ?_⟩
            show (t ^ m) • A.cls (k + 1) g hg = 0
            rw [cls_smul, cls_eq_zero_iff]
            refine ⟨a, (hj (k + 1)) ?_⟩
            rw [f.comm, ha, cx_smul_d, hh, map_smul]
      intro x₁ x₂ h
      obtain ⟨c, hc'⟩ := key (x₁ - x₂) (by rw [map_sub, h, sub_self])
      exact ⟨c, sub_eq_zero.mp (by simpa only [smul_sub] using hc')⟩
  refine localiseCx j.hom ?_ ?_ ?_ n
  · intro k x y hxy
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu
    subst hφ
    refine Subtype.ext (funext fun g => hu.injective ?_)
    exact congrFun (congrArg Subtype.val hxy) g
  · intro k
    constructor
    · intro x y hxy
      refine Subtype.ext (funext fun g => e.injective ?_)
      rw [he, he]
      exact congrFun (congrArg Subtype.val hxy) g
    · intro y
      refine ⟨⟨fun g => e.symm (y.1 g), e.symm.continuous.comp y.2⟩, Subtype.ext (funext fun g => ?_)⟩
      show t • e.symm (y.1 g) = y.1 g
      rw [← he, e.apply_symm_apply]
  · intro k x
    rcases j with ⟨φ, u, hφc, huc, heq⟩
    dsimp only at hφ hu hcov
    subst hφ
    have hx : Continuous x.1 := x.2
    let O : ℕ → Set (Fin k → G) := fun m => x.1 ⁻¹' ((fun v : V.V => t ^ m • v) ⁻¹' Set.range u)
    have hO : ∀ m, IsOpen (O m) := fun m =>
      ((hu.isOpen_range).preimage (continuous_const_smul _)).preimage hx
    have hmono : Monotone O := by
      refine monotone_nat_of_le_succ fun m g hg => ?_
      obtain ⟨l, hl⟩ := hg
      refine ⟨t • l, ?_⟩
      simp only at hl ⊢
      rw [map_smul, hl, pow_succ', mul_smul]
    have hcover : (Set.univ : Set (Fin k → G)) ⊆ ⋃ m, O m := by
      intro g _
      obtain ⟨m, l, hl⟩ := hcov (x.1 g)
      exact Set.mem_iUnion.2 ⟨m, l, hl⟩
    obtain ⟨m, hm⟩ := isCompact_univ.elim_directed_cover O hO hcover hmono.directed_le
    have hy : ∀ g, u (invFun u (t ^ m • x.1 g)) = t ^ m • x.1 g := fun g =>
      invFun_eq (hm (Set.mem_univ g))
    have hyc : Continuous fun g => invFun u (t ^ m • x.1 g) := by
      rw [hu.isEmbedding.continuous_iff]
      have : (u ∘ fun g => invFun u (t ^ m • x.1 g)) = fun g => t ^ m • x.1 g := funext hy
      rw [this]
      exact hx.const_smul _
    refine ⟨m, ⟨fun g => invFun u (t ^ m • x.1 g), hyc⟩, Subtype.ext (funext fun g => ?_)⟩
    exact hy g

end ReciprocityTheory.Coh
