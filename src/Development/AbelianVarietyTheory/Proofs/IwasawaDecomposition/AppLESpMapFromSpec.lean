module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb

namespace GlobalTheory.FlagEmb.CellOpen

variable {O : Type} [CommRing O] {X P : Scheme.{0}} {N : ℕ} {k : Type} [Field k]

theorem top_le_of_mem {W : (Sp k).Opens} {x : Sp k} (hx : x ∈ W) : ⊤ ≤ W := fun y _ => by
  have : y = x := Subsingleton.elim (α := PrimeSpectrum k) y x
  exact this ▸ hx

theorem mem_basicOpen_fnOn (x : Sp k) (a : k) : x ∈ (Sp k).basicOpen (fnOn ⊤ a) ↔ a ≠ 0 := by
  rw [basicOpen_fnOn, top_inf_eq, mem_spOpen]
  have : x.asIdeal = ⊥ := congrArg PrimeSpectrum.asIdeal (Subsingleton.elim (α := PrimeSpectrum k) x ⊥)
  rw [this, Ideal.mem_bot]

theorem appLE_spMap_fromSpec {U : X.Opens} (hU : IsAffineOpen U) {A : Type} [CommRing A] (φ : Γ(X, U) →+* A)
    {x : Sp A ⟶ X} (hx : x = spMap φ ≫ hU.fromSpec) (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    (x.appLE U ⊤ h).hom a = fnOn ⊤ (φ a) := by
  subst hx
  have e := appLE_appLE (spMap φ) hU.fromSpec hU.fromSpec_preimage_self.ge (le_rfl : ⊤ ≤ spMap φ ⁻¹ᵁ ⊤) a
  refine e.symm.trans ?_
  rw [fromSpec_appLE_self]
  have e2 := congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (R := Γ(X, U)) (S := .of A) (CommRingCat.ofHom φ))
  refine Eq.trans ?_ (congrArg (resG (Sp A) (le_top : (⊤ : (Sp A).Opens) ≤ ⊤)) e2.symm)
  rfl

def sec (p0 : P ⟶ X) (g : P ⟶ PSpace O N) (U : X.Opens) (a : Fin (N + 1) → Γ(X, U)) (r : Fin (N + 1)) :
    Γ(P, p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r) :=
  ∑ q, (p0.appLE U _ inf_le_left).hom (a q) * pullRatio g _ r inf_le_right q

theorem appLE_sec (p0 : P ⟶ X) (g : P ⟶ PSpace O N) {U : X.Opens} (hU : IsAffineOpen U) (a : Fin (N + 1) → Γ(X, U))
    (r : Fin (N + 1)) (z : Sp k ⟶ P) (φ : Γ(X, U) →+* k) (hφ : z ≫ p0 = spMap φ ≫ hU.fromSpec) (b : O →+* k)
    (v : Fin (N + 1) → k) (hv) (hz : z ≫ g = pt b v hv) (h : ⊤ ≤ z ⁻¹ᵁ (p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r)) :
    v r ≠ 0 ∧ (z.appLE _ ⊤ h).hom (sec p0 g U a r) = fnOn ⊤ ((∑ q, φ (a q) * v q) / v r) := open MvPolynomial GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.ProjFrac in by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := O)
  have pre : pt b v hv ⁻¹ᵁ chart O N r = spOpen (v r) := by
    change ProjPoint.ofHom (grading O N) (eval₂Hom b v) (map_irrelevant_eval₂Hom b hv) ⁻¹ᵁ
      Proj.basicOpen (grading O N) (MvPolynomial.X r) = _
    rw [ProjPoint.ofHom_preimage_basicOpen _ _ _ one_pos (isHomogeneous_X O r), eval₂Hom_X']
    rfl
  have from_chart : (isAffineOpen_chart O N r).fromSpec =
      Spec.map (Proj.awayToSection (grading O N) (MvPolynomial.X r)) ≫
        Proj.awayι (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos := by
    rw [IsAffineOpen.fromSpec, Iso.inv_comp_eq, Proj.awayι, ← Category.assoc, ← Category.assoc]
    refine (Category.id_comp _).symm.trans (congrArg (· ≫ _) ?_)
    exact (Proj.basicOpenIsoSpec (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos).hom_inv_id.symm
  have away_ratio (q : Fin (N + 1)) :
      (Proj.awayToSection (grading O N) (MvPolynomial.X r)).hom (ratioAway O N r q) = ratio O N r q := by
    rw [ratioAway, awayToSection_mk]
    exact frac_eq (by ring)
  have h2 : ⊤ ≤ pt b v hv ⁻¹ᵁ chart O N r := hz ▸ h.trans (z.preimage_mono inf_le_right)
  have hr : v r ≠ 0 := by
    have := h2 (Set.mem_univ (IsLocalRing.closedPoint k))
    rw [pre] at this
    intro e
    exact (mem_spOpen.1 this) (e ▸ zero_mem _)
  have ratio_mul (q : Fin (N + 1)) :
      pullRatio (pt b v hv) ⊤ r h2 q * fnOn ⊤ (v r) = fnOn ⊤ (v q) := by
    have hu' : IsUnit (eval₂Hom b v (MvPolynomial.X r)) := by rw [eval₂Hom_X']; exact IsUnit.mk0 _ hr
    have h4 := ProjPoint.awayLift_mk_mul (grading O N) (eval₂Hom b v) hu' (X_mem O N r) 1 (MvPolynomial.X q) (X_mem O N q)
    have he : pt b v hv = spMap (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫ _ :=
      ProjPoint.ofHom_eq_awayι _ _ _ one_pos (X_mem O N r) hu'
    have : IsIso (Proj.awayToSection (grading O N) (MvPolynomial.X r)) :=
      (Proj.basicOpenIsoAway (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos).isIso_hom
    have he2 : spMap (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫
        Proj.awayι (grading O N) (MvPolynomial.X r) (X_mem O N r) one_pos =
        ofChartHom r (inv (Proj.awayToSection (grading O N) (MvPolynomial.X r)) ≫
          CommRingCat.ofHom (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu') ≫
          (Scheme.ΓSpecIso (.of k)).inv) := by
      rw [ofChartHom, from_chart, ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc, Spec.map_comp, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv_assoc]
    rw [pullRatio_of_eq he h2 (he ▸ h2), pullRatio_of_eq he2 _ (ofChartHom_preimage _ _),
      pullRatio, ofChartHom_appLE, ← away_ratio, ← CommRingCat.comp_apply, IsIso.hom_inv_id_assoc,
      ]
    change (Scheme.ΓSpecIso (.of k)).inv.hom
      (ProjPoint.awayLift (grading O N) (eval₂Hom b v) (MvPolynomial.X r) hu' (ratioAway O N r q)) * _ = _
    rw [← resG_self (X := Sp k) le_top ((Scheme.ΓSpecIso (.of k)).inv.hom _)]
    change fnOn ⊤ _ * fnOn ⊤ _ = fnOn ⊤ _
    rw [← map_mul]
    exact congrArg _ (by simpa only [ratioAway, eval₂Hom_X', pow_one] using h4)
  refine ⟨hr, ((IsUnit.mk0 _ hr).map (fnOn ⊤)).mul_right_cancel ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_mul, div_mul_cancel₀ _ hr, sec, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, map_mul, appLE_appLE, appLE_spMap_fromSpec hU φ hφ, appLE_pullRatio, pullRatio_of_eq hz _ h2, mul_assoc,
    ratio_mul]

def linOpen (p0 : P ⟶ X) (g : P ⟶ PSpace O N) (U : X.Opens) (a : Fin (N + 1) → Γ(X, U)) : P.Opens :=
  ⨆ r, P.basicOpen (sec p0 g U a r)

theorem mem_linOpen_iff (p0 : P ⟶ X) (g : P ⟶ PSpace O N) {U : X.Opens} (hU : IsAffineOpen U)
    (a : Fin (N + 1) → Γ(X, U)) (z : Sp k ⟶ P) (φ : Γ(X, U) →+* k) (hφ : z ≫ p0 = spMap φ ≫ hU.fromSpec) (b : O →+* k)
    (v : Fin (N + 1) → k) (hv) (hz : z ≫ g = pt b v hv) (x : Sp k) :
    z x ∈ linOpen p0 g U a ↔ ∑ q, φ (a q) * v q ≠ 0 := by
  have key : ∀ r (h : ⊤ ≤ z ⁻¹ᵁ (p0 ⁻¹ᵁ U ⊓ g ⁻¹ᵁ chart O N r)),
      z x ∈ P.basicOpen (sec p0 g U a r) ↔ ∑ q, φ (a q) * v q ≠ 0 := fun r h => by
    obtain ⟨hr, e⟩ := appLE_sec p0 g hU a r z φ hφ b v hv hz h
    have e2 := Scheme.basicOpen_appLE z ⊤ _ h (sec p0 g U a r)
    rw [top_inf_eq] at e2
    refine (iff_of_eq (congrArg (x ∈ ·) e2)).symm.trans ?_
    refine (iff_of_eq (congrArg (fun t => x ∈ (Sp k).basicOpen t) e)).trans ?_
    rw [mem_basicOpen_fnOn, div_ne_zero_iff, and_iff_left hr]
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := Opens.mem_iSup.1 hx
    exact (key r (top_le_of_mem (x := x) (P.basicOpen_le _ hr))).1 hr
  · intro hx
    obtain ⟨r, hr⟩ := exists_mem_chart O N (g (z x))
    refine Opens.mem_iSup.2 ⟨r, (key r (top_le_of_mem (x := x) ⟨?_, hr⟩)).2 hx⟩
    change x ∈ (z ≫ p0) ⁻¹ᵁ U
    rw [hφ, Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    trivial

theorem exists_isCellOpen (O : Type) [CommRing O] (X P : Scheme.{0}) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ)
    (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (U : X.affineOpens)
    (D : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) : ∃ W : P.Opens, IsCellOpen p0 p U D w W := by
  let F : (Σ τ : T, Fin (m τ + 1)) → P.Opens := fun i =>
    linOpen p0 (p (stdEn i.1 i.2 (Nat.le_of_lt_succ i.2.2))) U.1 (lform D (wLet w ∘ std i.1 i.2 (Nat.le_of_lt_succ i.2.2)))
  refine ⟨p0 ⁻¹ᵁ U.1 ⊓ ⟨⋂ i, (F i : Set P), isOpen_iInter_of_finite fun i => (F i).2⟩, fun k _ z => ⟨fun h => ?_, ?_⟩⟩
  · have h1 : Set.range (z ≫ p0) ⊆ Set.range U.2.fromSpec := by
      rw [U.2.range_fromSpec]
      rintro _ ⟨x, rfl⟩
      exact (h ⟨x, rfl⟩).1
    have hi : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
    let l := IsOpenImmersion.lift U.2.fromSpec (z ≫ p0) h1
    have hφ : z ≫ p0 = spMap (Spec.preimage l).hom ≫ U.2.fromSpec :=
      (IsOpenImmersion.lift_fac _ _ h1).symm.trans (congrArg (· ≫ _) (Spec.map_preimage l).symm)
    refine ⟨(Spec.preimage l).hom, hφ, fun τ j hj b v hv hz => ?_⟩
    refine (mem_linOpen_iff p0 _ U.2 _ z _ hφ b v hv hz (IsLocalRing.closedPoint k)).1 ?_
    exact Set.mem_iInter.1 (h ⟨_, rfl⟩).2 ⟨τ, j, Nat.lt_succ_of_le hj⟩
  · rintro ⟨φ, hφ, H⟩ _ ⟨x, rfl⟩
    refine ⟨?_, Set.mem_iInter.2 fun i => ?_⟩
    · change x ∈ (z ≫ p0) ⁻¹ᵁ U.1
      rw [hφ, Scheme.Hom.comp_preimage, U.2.fromSpec_preimage_self]
      trivial
    · let y := z ≫ p (stdEn i.1 i.2 (Nat.le_of_lt_succ i.2.2))
      obtain ⟨v, hv, e⟩ := exists_eq_pt (Spec.preimage (y ≫ PSpace.str _ _)).hom y (Spec.map_preimage _).symm
      exact (mem_linOpen_iff p0 _ U.2 _ z φ hφ _ v hv e x).2 (H _ _ _ _ v hv e)

end GlobalTheory.FlagEmb.CellOpen
