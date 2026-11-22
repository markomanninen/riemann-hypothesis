module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratesOfCloseLocalEquationClassicalPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generates_of_close_localEquation_classicalPoint :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
      (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z),
      M₁.IsHom M (AlgHom.id o Ω) π →
      ∀ (U : M.Z.Opens) (D : EffCartierData M.Z),
        (∀ x ∈ (GlobalTheory.EffCartierData.idealSheaf D).support, x ∉ U) →
        ∀ (x : M.Z) (p : ℕ) [Fact p.Prime] (y₀ : Sp (OO p) ⟶ M.Z),
          M.Cen U x y₀ → ∀ f, EqAt M D x f →
          ∃ k : ℕ, ∀ (G b : M₁.O (π x)),
            ‖RatModel.val M (gPt p ≫ y₀) ((G : Ω) + b)‖ = ‖RatModel.val M (gPt p ≫ y₀) f‖ →
            b ∈ Ideal.span {c : M₁.O (π x) | ¬ IsUnit c} ^ k →
            (G : Ω) / f ∈ M.O x → (G : Ω) ≠ 0 ∧ f / G ∈ M.O x := by
  intro o Ω _ _ _ _ M₁ M π hπ U D hD x p _ y₀ hy f hf
  obtain ⟨i, hxi, rfl⟩ := hf
  set F : Ω := valF M.pt (D.U i) (D.f i)
  set y : Sp (PadicAlgCl p) ⟶ M.Z := gPt p ≫ y₀ with hydef

  have hFO : F ∈ M.O x := RatModel.valF_mem_O hxi _
  have hwx : y (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ x := RatModel.gPt_specializes hy.1 _
  have hwU : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ U := hy.2 ⟨_, rfl⟩
  have hwi : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ D.U i := hwx.mem_open (D.U i).isOpen hxi
  have hwb : y (IsLocalRing.closedPoint (PadicAlgCl p)) ∈ M.Z.basicOpen (D.f i) := by
    by_contra h
    exact hD _ ((D.mem_support_iff i hwi).2 h) hwU
  have hF0 : RatModel.val M y F ≠ 0 :=
    (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton y (IsLocalRing.closedPoint (PadicAlgCl p)))
      ⟨_, RatModel.valF_mem_O hwi _⟩).2 ((RatModel.isUnit_valF_iff hwi (D.f i)).2 hwb)
  have hFpos : 0 < ‖RatModel.val M y F‖₊ := nnNorm_pos.2 hF0

  have hle : M₁.O (π x) ≤ M.O x := fun c hc => hπ.map_mem_O hc
  let v : M₁.O (π x) →+* PadicAlgCl p :=
    (RatModel.valHomOf y x (RatModel.gPt_specializes hy.1)).comp (Subalgebra.inclusion hle).toRingHom
  have hv_apply : ∀ c : M₁.O (π x), v c = RatModel.val M y c := fun c => rfl
  have hv1 : ∀ c, ‖v c‖₊ ≤ 1 := fun c => by
    rw [← NNReal.coe_le_coe, coe_nnNorm, NNReal.coe_one, hv_apply]
    exact RatModel.norm_val_le_one hy.1 (hle c.2)
  have hvlt : ∀ c : M₁.O (π x), ¬ IsUnit c → ‖v c‖₊ < 1 := by
    intro c hc
    have hc' : (c : Ω) ∈ M₁.O (π (y (IsLocalRing.closedPoint (PadicAlgCl p)))) :=
      RatModel.O_le_of_specializes (hwx.map π.continuous) c.2
    have e := hπ.val_comp y (IsLocalRing.closedPoint (PadicAlgCl p)) hc'
    have hc0 : (y₀ ≫ π) (cPt p) = π x := by rw [Scheme.Hom.comp_apply, hy.1]
    have h1 := (RatModel.norm_val_lt_one_iff hc0 c.2).2 hc
    rw [← Category.assoc, ← hydef, e] at h1
    rw [← NNReal.coe_lt_coe, coe_nnNorm, NNReal.coe_one, hv_apply]
    exact h1

  have : IsDedekindDomain o := ArithBase.ded (Ω := Ω)
  have := M₁.lft
  have : IsLocallyNoetherian M₁.Z := LocallyOfFiniteType.isLocallyNoetherian M₁.s
  have : IsNoetherianRing (M₁.O (π x)) := isNoetherianRing_of_ringEquiv _ (M₁.stalkEquiv (π x))
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (maximalIdeal (M₁.O (π x)))
  set ρ : NNReal := s.sup fun c => ‖v c‖₊
  have hρ : ρ < 1 := by
    refine (Finset.sup_lt_iff (by simp)).2 fun c hc => hvlt c ?_
    have : c ∈ maximalIdeal (M₁.O (π x)) := hs ▸ Submodule.subset_span hc
    exact (mem_maximalIdeal c).1 this
  have hm : ∀ c ∈ maximalIdeal (M₁.O (π x)), ‖v c‖₊ ≤ ρ := by
    rw [← hs]
    exact nnnorm_le_of_mem_span v hv1 fun c hc => Finset.le_sup (f := fun c => ‖v c‖₊) hc
  have hspan : Ideal.span {c : M₁.O (π x) | ¬ IsUnit c} = maximalIdeal (M₁.O (π x)) := by
    have : {c : M₁.O (π x) | ¬ IsUnit c} = (maximalIdeal (M₁.O (π x)) : Set (M₁.O (π x))) :=
      Set.ext fun c => (mem_maximalIdeal c).symm
    rw [this, Ideal.span_eq]
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hFpos hρ
  refine ⟨k, fun G b hGb hb hGf => ?_⟩

  rw [hspan] at hb
  have hbk : ‖RatModel.val M y b‖₊ < ‖RatModel.val M y F‖₊ :=
    lt_of_le_of_lt (nnnorm_le_pow_of_mem_pow v hv1 hm k b hb) hk
  have hadd : RatModel.val M y ((G : Ω) + b) = RatModel.val M y G + RatModel.val M y b :=
    RatModel.val_add (RatModel.gPt_specializes hy.1) (hle G.2) (hle b.2)
  have hGb' : ‖RatModel.val M y G + RatModel.val M y b‖₊ = ‖RatModel.val M y F‖₊ := by
    rw [← hadd]
    exact NNReal.eq hGb
  have hG : ‖RatModel.val M y G‖₊ = ‖RatModel.val M y F‖₊ := by
    refine le_antisymm ?_ ?_
    · have e : RatModel.val M y G = (RatModel.val M y G + RatModel.val M y b) + -RatModel.val M y b := by ring
      rw [e]
      refine (IsUltrametricDist.nnNorm_add_le_max _ _).trans (max_le hGb'.le ?_)
      rw [nnNorm_neg]
      exact hbk.le
    · rw [← hGb']
      refine (IsUltrametricDist.nnNorm_add_le_max _ _).trans (max_le le_rfl ?_)
      by_contra h
      push Not at h
      have := (IsUltrametricDist.nnNorm_add_le_max (RatModel.val M y G) (RatModel.val M y b)).trans
        (max_le h.le le_rfl)
      rw [hGb'] at this
      exact absurd hbk (not_lt.2 this)
  have hG0 : (G : Ω) ≠ 0 := by
    intro h
    rw [h, RatModel.val_zero, nnNorm_zero] at hG
    exact hFpos.ne hG
  have hFne : F ≠ 0 := by
    intro h
    rw [h, RatModel.val_zero] at hF0
    exact hF0 rfl
  refine ⟨hG0, ?_⟩
  have hmul : RatModel.val M y ((G : Ω) / F * F) = RatModel.val M y ((G : Ω) / F) * RatModel.val M y F :=
    RatModel.val_mul (RatModel.gPt_specializes hy.1) hGf hFO
  rw [div_mul_cancel₀ _ hFne] at hmul
  have hq : ‖RatModel.val M y ((G : Ω) / F)‖₊ = 1 := by
    have h2 : ‖RatModel.val M y ((G : Ω) / F)‖₊ * ‖RatModel.val M y F‖₊ = 1 * ‖RatModel.val M y F‖₊ := by
      rw [one_mul, ← nnNorm_mul, ← hmul, hG]
    exact mul_right_cancel₀ hFpos.ne' h2
  have hq' : ‖RatModel.val M (gPt p ≫ y₀) ((G : Ω) / F)‖ = 1 := by
    rw [← coe_nnNorm]
    exact congrArg NNReal.toReal hq
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.norm_val_eq_one_iff hy.1 hGf).1 hq')
  simpa [inv_div] using hu.2
