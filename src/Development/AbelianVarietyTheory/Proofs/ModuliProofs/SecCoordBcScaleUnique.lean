module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.Coord
open GlobalTheory.ZM.RepBC

theorem le_iSup_chart {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) : (⊤ : Y.Opens) ≤ iSup L.U := hL.cover.ge

theorem exists_global_unit {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {t t' : L.Gen} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ j, t.s j = res (le_top : L.U j ≤ ⊤) w * t'.s j := by
  let u : ∀ j, Γ(Y, L.U j)ˣ := fun j => t.s j * (t'.s j)⁻¹
  have compat : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (u i) =
      res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (u j) := by
    intro i j
    simp only [u, map_mul, map_inv, ht i j, ht' i j, mul_inv]
    simp only [_root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
  have glue : ∀ (v : ∀ j, Γ(Y, L.U j)ˣ),
      (∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (v i) =
        res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (v j)) →
      ∃ s : Γ(Y, ⊤), ∀ j, resG Y (le_top : L.U j ≤ ⊤) s = (v j).val := by
    intro v hv
    exact (TopCat.Sheaf.existsUnique_gluing' Y.sheaf L.U ⊤ (fun _ => homOfLE le_top) (le_iSup_chart hL) _ (by
        intro i j
        exact congrArg Units.val (hv i j))).exists
  obtain ⟨s, hs⟩ := glue u compat
  have compat' : ∀ i j, res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) ((u i)⁻¹) =
      res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) ((u j)⁻¹) := by
    intro i j
    rw [map_inv, map_inv, compat]
  obtain ⟨s', hs'⟩ := glue (fun j => (u j)⁻¹) compat'
  have hss : s * s' = 1 := by
    apply Y.sheaf.eq_of_locally_eq' L.U ⊤ (fun _ => homOfLE le_top) (le_iSup_chart hL)
    intro j
    change resG Y (le_top : L.U j ≤ ⊤) (s * s') = resG Y (le_top : L.U j ≤ ⊤) 1
    rw [map_mul, map_one, hs, hs']
    exact Units.mul_inv (u j)
  let w : Γ(Y, ⊤)ˣ := ⟨s, s', hss, by simpa [mul_comm] using hss⟩
  refine ⟨w, fun j => ?_⟩
  have hw : res (le_top : L.U j ≤ ⊤) w = u j := Units.ext (hs j)
  rw [hw]
  change t.s j = (t.s j * (t'.s j)⁻¹) * t'.s j
  simp

theorem appLE_spec {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (e : (⊤ : (Sp R').Opens) ≤ spMap φ ⁻¹ᵁ ⊤)
    (a : R) : ((spMap φ).appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (φ a) := by
  have h := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  refine Eq.trans ?_ h.symm
  exact r_self (X := Sp R') (U := ⊤) le_rfl (((spMap φ).app ⊤).hom _)

variable {X : Scheme.{0}} {M : LB X} {I : Type} {th : I → M.Sec} {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : I → R}

theorem baseChange (h : SecCoord M th x v) {R' : Type} [CommRing R'] (φ : R →+* R') :
    SecCoord M th (spMap φ ≫ x) (fun i => φ (v i)) := by
  obtain ⟨τ, hτ, h⟩ := h
  refine ⟨LB.pullGen M _ _ τ (spMap φ), ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen M _ _ τ hτ _, fun i j e => ?_⟩
  have hle : (M.pull (spMap φ ≫ x)).U j ≤ spMap φ ⁻¹ᵁ (M.pull x).U j :=
    fun _ hy => le_pull M x j (e hy)
  have h0 := congrArg ((spMap φ).appLE _ _ hle).hom (h i j (pull_le M x j))
  rw [map_mul, appLE_appLE _ _ _ _ e, appLE_r] at h0
  refine h0.trans ?_
  congr 1
  rw [← appLE_spec φ le_top]
  exact (r_appLE (spMap φ) _ _ _).symm

theorem scale (h : SecCoord M th x v) (u : Rˣ) : SecCoord M th x (fun i => u * v i) := by
  obtain ⟨τ, hτ, h⟩ := h
  let w : Γ(Sp R, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u
  refine ⟨⟨fun j => (res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹ * τ.s j⟩, fun j j' => ?_, fun i j e => ?_⟩
  · have e1 : res (inf_le_left : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j ≤ ⊤) w) =
        res (inf_le_right : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j' ≤ ⊤) w) :=
      Units.ext ((rr _ _ _).trans (rr _ _ _).symm)
    simp only [map_mul, map_inv]
    rw [hτ j j', e1, mul_left_comm]
  · rw [h i j e, map_mul, map_mul]
    have e1 : resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u) =
      (res (le_top : (M.pull x).U j ≤ ⊤) w).val := rfl
    rw [e1]
    show _ = _ * (((res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹).val * (τ.s j).val)
    rw [_root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]

theorem unique (hM : M.IsLB) (h : SecCoord M th x v) {v' : I → R} (h' : SecCoord M th x v') :
    ∃ u : Rˣ, ∀ i, v' i = u * v i := by
  obtain ⟨τ, hτ, h⟩ := h
  obtain ⟨τ', hτ', h'⟩ := h'
  have hcov : (⊤ : (Sp R).Opens) ≤ iSup (M.pull x).U := by
    intro y _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hM.cover.ge (show x y ∈ (⊤ : X.Opens) from trivial))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
  have global : ∃ w : Γ(Sp R, ⊤)ˣ, ∀ j, τ.s j = res (le_top : (M.pull x).U j ≤ ⊤) w * τ'.s j := by
    let u : ∀ j, Γ((Sp R), (M.pull x).U j)ˣ := fun j => τ.s j * (τ'.s j)⁻¹
    have compat : ∀ i j, res (inf_le_left : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U i) (u i) =
        res (inf_le_right : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U j) (u j) := by
      intro i j
      simp only [u, map_mul, map_inv, hτ i j, hτ' i j, mul_inv]
      simp only [_root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
    have glue : ∀ (v : ∀ j, Γ((Sp R), (M.pull x).U j)ˣ),
        (∀ i j, res (inf_le_left : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U i) (v i) =
          res (inf_le_right : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U j) (v j)) →
        ∃ s : Γ((Sp R), ⊤), ∀ j, resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) s = (v j).val := by
      intro v hv
      exact (TopCat.Sheaf.existsUnique_gluing' (Sp R).sheaf (M.pull x).U ⊤ (fun _ => homOfLE le_top) hcov _ (by
          intro i j
          exact congrArg Units.val (hv i j))).exists
    obtain ⟨s, hs⟩ := glue u compat
    have compaτ' : ∀ i j, res (inf_le_left : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U i) ((u i)⁻¹) =
        res (inf_le_right : (M.pull x).U i ⊓ (M.pull x).U j ≤ (M.pull x).U j) ((u j)⁻¹) := by
      intro i j
      rw [map_inv, map_inv, compat]
    obtain ⟨s', hs'⟩ := glue (fun j => (u j)⁻¹) compaτ'
    have hss : s * s' = 1 := by
      apply (Sp R).sheaf.eq_of_locally_eq' (M.pull x).U ⊤ (fun _ => homOfLE le_top) hcov
      intro j
      change resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) (s * s') = resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) 1
      rw [map_mul, map_one, hs, hs']
      exact Units.mul_inv (u j)
    let w : Γ((Sp R), ⊤)ˣ := ⟨s, s', hss, by simpa [mul_comm] using hss⟩
    refine ⟨w, fun j => ?_⟩
    have hw : res (le_top : (M.pull x).U j ≤ ⊤) w = u j := Units.ext (hs j)
    rw [hw]
    change τ.s j = (τ.s j * (τ'.s j)⁻¹) * τ'.s j
    simp
  obtain ⟨w, hw⟩ := global
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, fun i => ?_⟩
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v' i) =
      w.val * (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i) := by
    apply (Sp R).sheaf.eq_of_locally_eq' (M.pull x).U ⊤ (fun _ => homOfLE le_top) hcov
    intro j
    have e := (h' i j (pull_le M x j)).symm.trans (h i j (pull_le M x j))
    rw [hw j] at e
    show resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _ = resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _
    rw [map_mul]
    apply (Units.mul_left_inj (τ'.s j)).1
    refine e.trans ?_
    show _ * (resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) w.val * (τ'.s j).val) = _
    ring
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom key
  rw [map_mul] at this
  simpa using this

theorem secCoord_bc_scale_unique : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), M.IsLB → SecCoord M th x v → (∀ (R' : Type) [CommRing R'] (φ : R →+* R'), SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) ∧ (∀ u : Rˣ, SecCoord M th x (fun i => u * v i)) ∧ ∀ v', SecCoord M th x v' → ∃ u : Rˣ, ∀ i, v' i = u * v i :=
  fun _ _ _ _ _ _ _ _ hM h => ⟨fun _ _ φ => baseChange h φ, scale h, fun _ h' => unique hM h h'⟩

end GlobalTheory.ZM.Coord
end
