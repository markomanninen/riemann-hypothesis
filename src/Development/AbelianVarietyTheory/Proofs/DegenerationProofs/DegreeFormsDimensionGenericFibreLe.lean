module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.FormCount

section Values
variable {F : Type} [CommRing F] {X Y : Scheme.{0}}

theorem valR_appLE (x : Sp F ⟶ Y) (φ : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ φ ⁻¹ᵁ U)
    (f : Γ(X, U)) (hx : ⊤ ≤ x ⁻¹ᵁ V) : valR x V ((φ.appLE U V h).hom f) = valR (x ≫ φ) U f := by
  have hx' : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U := le_trans hx (x.preimage_mono h)
  rw [CrdCalc.valR_eq _ _ hx, CrdCalc.valR_eq _ _ hx', CrdCalc.valHom, CrdCalc.valHom,
    ← Scheme.Hom.appLE_comp_appLE x φ U V ⊤ h hx]
  rfl

theorem valR_scal {K : Type} [CommRing K] (ψ : K →+* F) (x : Sp F ⟶ Y) (q : Y ⟶ Sp K) (hq : x ≫ q = spMap ψ)
    (V : Y.Opens) (hx : ⊤ ≤ x ⁻¹ᵁ V) (c : K) : valR x V (resTop V (scal q c)) = ψ c := by
  have e : valR x V (resTop V (scal q c)) =
      valR (x ≫ q) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c) :=
    valR_appLE x q ⊤ V le_top _ hx
  have e' := (CrdCalc.valR_spMap ψ (𝟙 (Sp K)) ⊤ le_rfl).2 ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom c)
  rw [Category.comp_id] at e'
  rw [e, hq, e', CrdCalc.valR_eq _ _ le_top]
  have h : (𝟙 (Sp K) : Sp K ⟶ Sp K).appLE ⊤ ⊤ le_top = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  congr 1
  change (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (((𝟙 (Sp K) : Sp K ⟶ Sp K).appLE ⊤ ⊤ le_top).hom _) = c
  rw [h]
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).inv_hom_id_apply c

theorem wchart_le (L : LB X) (φ : Y ⟶ X) (j : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => φ) j ≤ φ ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 X) j :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k

theorem exists_monomial (L : LB X) (φ : Y ⟶ X) (N d : ℕ) {J : Type} [Fintype J]
    (σ : J → (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (N : ℤ))).Sec) (α : J → ℕ) (hα : ∑ i, α i = d) :
    ∃ s : (LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => ((N * d : ℕ) : ℤ))).Sec,
      ∀ j, s.f j = ∏ i, (φ.appLE _ _ (wchart_le L φ j)).hom ((σ i).f j) ^ α i := by
  have pull_restrict {U U' : X.Opens} {V V' : Y.Opens} (hu : U' ≤ U) (hv : V' ≤ V)
      (h : V ≤ φ ⁻¹ᵁ U) (h' : V' ≤ φ ⁻¹ᵁ U') (a : Γ(X, U)) :
      (Y.presheaf.map (homOfLE hv).op).hom ((φ.appLE U V h).hom a) =
        (φ.appLE U' V' h').hom ((X.presheaf.map (homOfLE hu).op).hom a) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  have transition {Z : Scheme.{0}} (f : Z ⟶ X) (j j' : Fin 1 → L.ι) (n : ℕ) :
      ((L.LinComb (fun _ : Fin 1 => f) (fun _ => (n : ℤ))).g j j').val =
        ((f.appLE _ _ (le_inf
          (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => f) j 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => f) j' 0)))).hom
          (L.g (j 0) (j' 0)).val) ^ n := by
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
    rfl
  let A (j : Fin 1 → L.ι) := L.wchart (fun _ : Fin 1 => 𝟙 X) j
  let B (j : Fin 1 → L.ι) := L.wchart (fun _ : Fin 1 => φ) j
  let s (i : J) (j : Fin 1 → L.ι) : Γ(X, A j) := (σ i).f j
  let m (j : Fin 1 → L.ι) : Γ(Y, B j) := ∏ i, (φ.appLE (A j) (B j) (wchart_le L φ j)).hom (s i j) ^ α i
  refine ⟨⟨m, ?_⟩, fun _ => rfl⟩
  rintro (j : Fin 1 → L.ι) (j' : Fin 1 → L.ι)
  let U := A j ⊓ A j'
  let V := B j ⊓ B j'
  have h : V ≤ φ ⁻¹ᵁ U := fun _ hy => ⟨wchart_le L φ j hy.1, wchart_le L φ j' hy.2⟩
  let p := (φ.appLE U V h).hom
  let gX : Γ(X, U) := ((L.LinComb (fun _ : Fin 1 => 𝟙 X) (fun _ => (N : ℤ))).g j j').val
  let gY : Γ(Y, V) := ((L.LinComb (fun _ : Fin 1 => φ) (fun _ => ((N * d : ℕ) : ℤ))).g j j').val
  have hg : p gX ^ d = gY := by
    dsimp only [p, gX, gY]
    rw [transition (𝟙 X) j j' N, transition φ j j' (N * d), map_pow, ← pow_mul,
      ← CommRingCat.comp_apply]
    erw [Scheme.Hom.appLE_comp_appLE φ (𝟙 X)]
    rfl
  let leftX := (X.presheaf.map (homOfLE (inf_le_left : U ≤ A j)).op).hom
  let rightX := (X.presheaf.map (homOfLE (inf_le_right : U ≤ A j')).op).hom
  have hc (i : J) : p (leftX (s i j)) = p gX * p (rightX (s i j')) := by
    rw [← map_mul]
    exact congrArg p ((σ i).compat j j')
  change (Y.presheaf.map (homOfLE (inf_le_left : V ≤ B j)).op).hom (m j) =
    gY * (Y.presheaf.map (homOfLE (inf_le_right : V ≤ B j')).op).hom (m j')
  simp only [m, map_prod, map_pow,
    pull_restrict (inf_le_left : U ≤ A j) (inf_le_left : V ≤ B j) (wchart_le L φ j) h,
    pull_restrict (inf_le_right : U ≤ A j') (inf_le_right : V ≤ B j') (wchart_le L φ j') h]
  change (∏ i, p (leftX (s i j)) ^ α i) = gY * ∏ i, p (rightX (s i j')) ^ α i
  simp only [hc, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hα, hg]

end Values

theorem hilb_le {k J : Type} [Field k] [Fintype J] (C : Set (J → k)) (d m : ℕ) (β : Fin m → C → k)
    (h : ∀ α : J → ℕ, ∑ i, α i = d → ∃ c : Fin m → k, ∀ v : C, ∏ i, v.1 i ^ α i = ∑ l, c l * β l v) :
    hilb C d ≤ m := by
  have le : (MvPolynomial.homogeneousSubmodule J k d).map
      (LinearMap.pi fun v : C => (MvPolynomial.aeval (R := k) v.1).toLinearMap) ≤ Submodule.span k (Set.range β) := by
    rintro _ ⟨P, hP, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [P.as_sum, map_sum]
    refine Submodule.sum_mem _ fun α hα => ?_
    have hd : ∑ i, α i = d := by
      have := MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hP hα
      rw [this]
      exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => Finsupp.notMem_support_iff.1 hi).symm
    obtain ⟨c, hc⟩ := h α hd
    refine (Submodule.mem_span_range_iff_exists_fun k).2 ⟨fun l => P.coeff α * c l, funext fun v => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.pi_apply, AlgHom.toLinearMap_apply,
      MvPolynomial.aeval_monomial, Algebra.algebraMap_self, RingHom.id_apply]
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), hc v, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => _root_.mul_assoc _ _ _
  have := Module.Finite.span_of_finite k (Set.finite_range β)
  exact (Submodule.finrank_mono le).trans ((finrank_range_le_card β).trans (Fintype.card_fin m).le)

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

theorem dim_eq (u : ρ.UTest p y₀) : u.A.g = S.g :=
  (ReciprocityTheory.ChartRestriction.G.H1.dim_unique u.A.A.hom u.A.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback u.cart.1 ρ.P.smoothDim)
    (eSec u.A.A (IsLocalRing.closedPoint _))).trans ρ.g_eq

theorem gPt_j (u : ρ.UTest p y₀) :
    gPt p ≫ spMap u.j = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem hilb_generic_le : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (J : Type) [Fintype J] (σ : J → (u.H S.N).Sec) (d : ℕ), 1 ≤ d → hilb {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ u.G.left, a ≫ u.G.hom = gPt p ≫ spMap u.j ∧ Crd (u.H S.N) σ a w} d ≤ (S.N * d) ^ S.g := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u J _ σ d hd
  have hN : 1 ≤ S.N * d := by
    rw [ρ.N_eq]
    exact Nat.mul_pos (pow_pos (pow_pos ρ.n_prime.pos _) _) hd
  obtain ⟨b, -, hb⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hL.1.secBaseChange u.V _ u.D u.A u.G
    u.U.toUnifPre (S.N * d) hN
  rw [← dim_eq u]
  let C := {w : J → PadicAlgCl p | ∃ a : Sp (PadicAlgCl p) ⟶ u.G.left,
    a ≫ u.G.hom = gPt p ≫ spMap u.j ∧ Crd (u.H S.N) σ a w}
  have hC : ∀ w : C, ∃ (x : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V)) (l : Fin 1 → u.U.LG.L.ι)
      (c : PadicAlgCl p), x ≫ pullback.snd _ _ = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ∧
      ⊤ ≤ x ⁻¹ᵁ LB.wchart u.U.LG.L (fun _ : Fin 1 => pullback.fst u.G.hom (jK u.V)) l ∧
      ∀ i, w.1 i = c * valR (x ≫ pullback.fst _ _) _ ((σ i).f l) := by
    rintro ⟨w, a, ha, l, c, hl, hw⟩
    obtain ⟨x, rfl, hx⟩ : ∃ x : Sp (PadicAlgCl p) ⟶ pullback u.G.hom (jK u.V), x ≫ pullback.fst _ _ = a ∧
        x ≫ pullback.snd _ _ = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) :=
      ⟨pullback.lift a _ (ha.trans (gPt_j u)), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    exact ⟨x, l, c, hx, fun y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (hl hy) k, hw⟩
  choose x l c hx hl hw using hC
  refine hilb_le C d _ (fun n w => c w ^ d * valR (x w) _ ((b n).f (l w))) fun α hα => ?_
  obtain ⟨s, hs⟩ := exists_monomial u.U.LG.L (pullback.fst u.G.hom (jK u.V)) S.N d σ α hα
  obtain ⟨e, he, -⟩ := hb s
  refine ⟨fun n => algebraMap _ _ (e n), fun w => ?_⟩
  have h := congrArg (CrdCalc.valHom (x w) _ (hl w)) ((hs (l w)).symm.trans (he (l w)))
  replace h := (map_prod _ _ _).symm.trans (h.trans (map_sum _ _ _))
  simp only [hw w, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hα]
  refine Eq.trans ?_ ((congrArg (c w ^ d * ·) h).trans ?_)
  · refine congrArg (c w ^ d * ·) (Finset.prod_congr rfl fun i _ => Eq.symm ((map_pow _ _ _).trans ?_))
    exact congrArg (· ^ α i) ((CrdCalc.valR_eq _ _ (hl w) _).symm.trans (valR_appLE _ _ _ _ _ _ (hl w)))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => Eq.trans (congrArg (c w ^ d * ·) ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (CrdCalc.valR_eq _ _ (hl w) _).symm))) (mul_left_comm _ _ _)
  exact (CrdCalc.valR_eq _ _ (hl w) _).symm.trans (valR_scal _ (x w) _ (hx w) _ (hl w) (e n))

end GlobalTheory.ZH.FormCount
end
