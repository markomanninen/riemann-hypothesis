module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDiagonalEntryTorusIntegralOfFlatMapNeZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open GlobalTheory.FinPl.LastDiag (add_smul_mx exists_idemAt jX_pX_mem_latA mxAt_smul smul_eq_self smul_isHalf' symplO_add_right')
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastDiagonalEntry_torus_integral_of_flatMap_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (LV : Lat B.V) (LV₀ : Lat B.V₀) (LW : Lat J.W) (LW₀ : Lat J.W₀) (v : Pl D), GoodBF ψ B J LV LV₀ LW LW₀ v → UnrAt s v → ∀ 𝔉, IsFlatBF s (· = v) 𝔉 → ∀ f, Vac ψ B.V J.W LV LW (· = v) f → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → J.d.levi t ∈ grpAt J.W (· = v) → 𝔉 (s.om (1, J.d.levi t) f) ≠ 0 → ∀ i : Fin ρ, i.1 + 1 = ρ → t.1 i i - 1 ∈ intAt D (· = v) := by
  intro D ψ ρ B J s LV LV₀ LW LW₀ v hG hU 𝔉 h𝔉 f hf t ht htG hne i hi
  have mxAt_mul_left : ∀ {D : D7} {P : Pl D → Prop} {a b c : ℕ} (y : Mx D a b) {x : Mx D b c} (hx : MxAt P x),
      MxAt P (y ⬝ x) := by
    intro D P a b c y x hx i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hx l j)

  have mxAt_mul_right : ∀ {D : D7} {P : Pl D → Prop} {a b c : ℕ} {x : Mx D a b} (hx : MxAt P x) (y : Mx D b c),
      MxAt P (x ⬝ y) := by
    intro D P a b c x hx y i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

  have wittExtZero_inclusionX_mem_homLatticeCompletion : ∀ {D : D7} {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) {LS : Lat S}
      {LS₀ : Lat S₀} {LT : Lat T} {LT₀ : Lat T₀} {v : Pl D} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
      (hS₀ : IsSelfDualC S₀ LS₀) (hmS : MonoAt dS LS LS₀ v) (hmT : MonoAt dT LT LT₀ v) {w : WO S₀ T}
      (hw : w ∈ latO S₀ T (LS₀ : Set _) (LT : Set _) (· = v)),
      dS.ext0 T (dT.incX S₀ (dT.pX ⬝ w)) ∈ latO S T (LS : Set _) (LT : Set _) (· = v) := by
    intro D S S₀ T T₀ ρ σ dS dT LS LS₀ LT LT₀ v hS hT hS₀ hmS hmT w hw
    have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
    refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT (· = v) _).2 ⟨?_, fun y hy => ?_⟩
    · rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply]
      exact mxAt_mul_right (mxAt_mul_left _ (mxAt_mul_left _ hx)) _
    · change (dT.jX * (dT.pX * w) * dS.p0) *ᵥ y ∈ latA T LT (· = v)
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have h1 : dS.p0 *ᵥ y ∈ latV S₀ LS₀ (· = v) := ((hmS y).1 hy).2.2
      exact jX_pX_mem_latA dT hmT (GlobalTheory.FinPl.LatMem.latO_maps hS₀ hw h1)

  have wittExtZero_inclusionX_smul : ∀ {D : D7} {S S₀ T T₀ : HSp D} {ρ σ : ℕ} (dS : HypDec S S₀ ρ) (dT : HypDec T T₀ σ) (c : AE D)
      (ξ : Mx D σ S₀.rank),
      dS.ext0 T (dT.incX S₀ (c • ξ)) = c • dS.ext0 T (dT.incX S₀ ξ) := by
    intro D S S₀ T T₀ ρ σ dS dT c ξ
    rw [HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply, HypDec.incX_apply, Matrix.mul_smul, Matrix.smul_mul]

  have incAdj_smul : ∀ {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (c : AE D) (y : Mx D S.rank ρ),
      d.incAdj S (c • y) = cA D c • d.incAdj S y := by
    intro D T T₀ ρ d S c y
    rw [HypDec.incAdj_apply, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incY_apply, adj_smul, Matrix.smul_mul,
      smul_comm (incA D (-D.host.xi0⁻¹)) (cA D c), Matrix.mul_smul]

  have symplO_incAdj_proj : ∀ {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Mx D S.rank ρ) (w : WO S T),
      symplO S T (d.incAdj S z) w = symplO S T (d.incAdj S z) (d.incX S (d.pX ⬝ w)) := by
    intro D T T₀ ρ d S z w
    have key : hO S T (d.incAdj S z) w = hO S T (d.incAdj S z) (d.incX S (d.pX ⬝ w)) := by
      rw [d.hO_coordT S, d.hO_coordT S]
      simp only [HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incX_apply, ← Matrix.mul_assoc, HypDec.pX_jY,
        HypDec.p0_jY, HypDec.pY_jY, HypDec.pX_jX, HypDec.p0_jX, HypDec.pY_jX, Matrix.zero_mul, Matrix.one_mul]
      simp [pairT, hO]
    rw [symplO, symplO, key]

  have fix_char : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J)
      {P : Pl D → Prop} {𝔉 : (WO B.V J.W → ℂ) → (WO B.V₀ J.W₀ → ℂ)} (h𝔉 : IsFlatBF s P 𝔉) {f : WO B.V J.W → ℂ}
      (hθ : IsThetaFunO ψ B.V J.W f) (t : GL (Fin ρ) (AE D)) (hne : 𝔉 (s.om (1, J.d.levi t) f) ≠ 0)
      (ξ : Mx D ρ B.V₀.rank) (hξ : MxAt P ξ) (hfix : heisO ψ B.V J.W (B.d.ext0 J.W (J.d.incX B.V₀ ξ)) f = f),
      ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (t.1 ⬝ ξ))) = 1 := by
    intro D ψ ρ B J s P 𝔉 h𝔉 f hθ t hne ξ hξ hfix
    have hg : IsThetaFunO ψ B.V J.W (s.om (1, J.d.levi t) f) := s.weil.om_pres _ _ hθ
    have hact : actO B.V J.W 1 (J.d.levi t) (B.d.ext0 J.W (J.d.incX B.V₀ ξ)) =
        B.d.ext0 J.W (J.d.incX B.V₀ (t.1 ⬝ ξ)) := by
      rw [actO_eq, inv_one, mt_one, Matrix.mul_one, HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.incX_apply,
        HypDec.incX_apply, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, HypDec.levi_jX]
    have h1 := s.weil.om_heis 1 (J.d.levi t) (B.d.ext0 J.W (J.d.incX B.V₀ ξ)) f hθ
    rw [hfix, hact] at h1
    have h3 := h𝔉.Heisenberg₂.iso _ hg (t.1 ⬝ ξ) (mxAt_mul_left _ hξ)
    rw [← h1] at h3
    by_contra hc
    apply hne
    funext w
    have hw := congrFun h3 w
    rw [Pi.smul_apply, smul_eq_mul] at hw
    have h4 : (ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (t.1 ⬝ ξ))) - 1) *
        𝔉 (s.om (1, J.d.levi t) f) w = 0 := by
      rw [sub_mul, ← hw, one_mul, sub_self]
    exact (mul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hc)

  have yZero_mul_diag : ∀ {D : D7} (S : HSp D) {ρ : ℕ} (z : Fin S.rank → D.host.E) (t : Matrix (Fin ρ) (Fin ρ) (AE D))
      (ht : ∀ i j, i ≠ j → t i j = 0) (i : Fin ρ) (hi : i.1 + 1 = ρ),
      yZero S ρ z ⬝ t = t i i • yZero S ρ z := by
    intro D S ρ z t ht i hi
    classical
    have hell : ∀ j : Fin ρ, ell D ρ j = if j = i then 1 else 0 := fun j => by
      by_cases hj : j = i
      · subst hj; simp [ell, hi]
      · have hj' : ¬ (j.1 + 1 = ρ) := fun h => hj (Fin.ext (by omega))
        simp [ell, hj', hj]
    ext k l
    have hy : ∀ j, yZero S ρ z k j = if j = i then -ratV z k else 0 := fun j => by
      simp only [yZero, zEll, Matrix.neg_apply, Matrix.vecMulVec_apply, hell]
      split_ifs <;> simp
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, hy l]
    simp only [hy, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    by_cases hl : l = i
    · subst hl
      rw [ite_eq_left rfl, mul_comm]
    · rw [ite_eq_right hl, ht i l (Ne.symm hl), mul_zero, mul_zero]

  have symplO_incAdj_eq : ∀ {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D) (z : Mx D S.rank ρ) (w : WO S T),
      symplO S T (d.incAdj S z) w = -Algebra.trace (AF D.host.F) (AE D) (z ⬝ (d.pX ⬝ w)).trace := by
    intro D T T₀ ρ d S z w
    rw [symplO_incAdj_proj, GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj]

  have chi_add : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
      (y : Mx D S.rank ρ) (t : Matrix (Fin ρ) (Fin ρ) (AE D)) (ξ₁ ξ₂ : Mx D ρ S.rank),
      ψ (symplO S T (d.incAdj S y) (d.incX S (t ⬝ (ξ₁ + ξ₂)))) =
        ψ (symplO S T (d.incAdj S y) (d.incX S (t ⬝ ξ₁))) * ψ (symplO S T (d.incAdj S y) (d.incX S (t ⬝ ξ₂))) := by
    intro D ψ T T₀ ρ d S y t ξ₁ ξ₂
    rw [Matrix.mul_add, map_add (f := _), symplO_add_right', AddChar.map_add_eq_mul]

  obtain ⟨hθ, h2, hh⟩ := hf
  have hstd : IsStdChar D ψ (-1) := s.weil.std
  obtain ⟨eV, heV_int, heV_act, heV_cA, hhalf⟩ := exists_idemAt D v
  have heV_id : eV ∈ idAt D (· = v) := heV_int.1
  have hcA : ∀ c ∈ idAt D (· = v), cA D c ∈ idAt D (· = v) := fun c hc => by
    rw [← heV_act c hc, map_mul, heV_cA]; exact Ideal.mul_mem_left _ _ heV_id
  have hMx : ∀ c ∈ idAt D (· = v), MxAt (· = v) (J.d.incAdj B.V₀ (c • yZero B.V₀ ρ (vecB B.o B.ζ))) :=
    fun c hc k l => by
      rw [incAdj_smul, Matrix.smul_apply, smul_eq_mul]; exact Ideal.mul_mem_right _ _ (hcA c hc)

  have hcong := (GlobalTheory.IwaPlace.mem_congGrp_iff J.W (idAt D (· = v)) _).1 htG
  have hM : MxAt (· = v) (mt J.W (J.d.levi t) - 1) := fun k l => by rw [Matrix.sub_apply]; exact hcong k l
  have htM : t.1 - 1 = J.d.pX ⬝ (mt J.W (J.d.levi t) - 1) ⬝ J.d.jX := by
    rw [Matrix.mul_sub, Matrix.sub_mul, J.d.pX_levi t, Matrix.mul_one, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one]
  have ha : t.1 i i - 1 ∈ idAt D (· = v) := by
    have := mxAt_mul_right (mxAt_mul_left J.d.pX hM) J.d.jX i i
    rwa [← htM, Matrix.sub_apply, Matrix.one_apply_eq] at this
  have hρ : 0 < ρ := by omega
  rw [← hG.last hρ _ ha]
  refine (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hstd B.V₀ J.W LV₀ LW hG.sdV₀ hG.sdW (· = v) _ (hMx _ ha)).2 fun u' hu' => ?_
  obtain ⟨ξ, hξdef⟩ : ∃ ξ, ξ = J.d.pX ⬝ u' := ⟨_, rfl⟩
  have hξ : MxAt (· = v) ξ := hξdef ▸ mxAt_mul_left _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu')
  have hu : B.d.ext0 J.W (J.d.incX B.V₀ ξ) ∈ latO B.V J.W (LV : Set _) (LW : Set _) (· = v) :=
    hξdef ▸ wittExtZero_inclusionX_mem_homLatticeCompletion B.d J.d hG.sdV hG.sdW hG.sdV₀ hG.monoV hG.monoW hu'
  have hξe : eV • ξ = ξ := smul_eq_self (fun a ha => (mul_comm eV a).trans (heV_act a ha)) hξ

  have hχ : ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (t.1 ⬝ ξ))) = 1 := by
    rcases hG.tame.2 with h2v | ⟨e, ε, he, hε, hes⟩
    · obtain ⟨c, hcc, hcl⟩ := hhalf h2v
      have hcu := hcl _ _ _ _ _ hu
      rw [← wittExtZero_inclusionX_smul] at hcu
      have hfix := h2 _ hcu
      rw [← map_nsmul (B.d.ext0 J.W), ← map_nsmul (J.d.incX B.V₀)] at hfix
      have h2c : 2 • (c • ξ) = ξ := by
        rw [two_nsmul, add_smul_mx, hcc, hξe]
      rw [h2c] at hfix
      exact fix_char s h𝔉 hθ t hne ξ hξ hfix
    · have hact := (GlobalTheory.FinPl.placeIdem_acts D v ε hε).1
      have hce := GlobalTheory.SplitScalar.isSplitIdem_conj he
      have hfixE : ∀ e' : AE D, IsSplitIdem D e' →
          heisO ψ B.V J.W (B.d.ext0 J.W (J.d.incX B.V₀ (e' • ξ))) f = f := by
        intro e' he'
        have hmem := GlobalTheory.LatticeStable.smul_mem_latO D B.V J.W _ _ (· = v) e'
          (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he'.1])) _ hu
        rw [← wittExtZero_inclusionX_smul] at hmem
        refine hh e' he' _ hmem ?_
        rw [wittExtZero_inclusionX_smul]
        exact smul_isHalf' he'.1 _
      have hMe : ∀ e' : AE D, MxAt (· = v) (e' • ξ) := fun e' => mxAt_smul e' hξ
      have h1 := fix_char s h𝔉 hθ t hne _ (hMe e) (hfixE e he)
      have h2' := fix_char s h𝔉 hθ t hne _ (hMe (cA D e)) (hfixE _ hce)
      have hsum : e • ξ + cA D e • ξ = ξ := by
        rw [add_smul_mx, hes]
        exact smul_eq_self (fun a ha => (hact a).1 ha) hξ
      have hk := chi_add ψ J.d B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ)) t.1 (e • ξ) (cA D e • ξ)
      rw [hsum, h1, h2', mul_one] at hk
      exact hk
  have hε' := (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D ψ hstd B.V₀ J.W LV₀ LW hG.sdV₀ hG.sdW (· = v) _ (hMx _ heV_id)).1
    ((hG.last hρ eV heV_id).2 heV_int) u' hu'
  rw [symplO_incAdj_eq, ← hξdef, Matrix.smul_mul, ← Matrix.mul_smul, hξe] at hε'
  have hχ' := hχ
  rw [GlobalTheory.SplitScalar.symplO_skew, HypDec.symplO_incX_incAdj, ← Matrix.mul_assoc,
    yZero_mul_diag _ _ t.1 ht i hi, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at hχ'
  have hT : ψ (Algebra.trace (AF D.host.F) (AE D) (yZero B.V₀ ρ (vecB B.o B.ζ) ⬝ ξ).trace) = 1 := by
    rw [AddChar.map_neg_eq_inv] at hε'
    exact inv_eq_one.1 hε'
  rw [symplO_incAdj_eq, ← hξdef, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, sub_mul, one_mul, map_sub, neg_sub,
    sub_eq_add_neg, AddChar.map_add_eq_mul, hT, hχ', one_mul]
