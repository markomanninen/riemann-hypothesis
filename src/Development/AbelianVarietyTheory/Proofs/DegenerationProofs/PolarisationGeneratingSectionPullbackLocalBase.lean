module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrict
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemNonzeroLocusOfPull
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData

namespace GlobalTheory.GeneratorPull

theorem exists_down {X : Scheme.{0}} {L : LB X} (s : H0 L 1) : ∃ t : L.Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z)
    (J : (Z ⟶ X) → L.ι), Good L z J → sval s r z J = gs r z (L.U (J r)) (t.f (J r)) := by
  have exists_pw_local : ∃ b : LB.Sec (AbLaw.pw L ((1 : ℕ) : ℤ)),
      ∀ (Z : Scheme.{0}) (q : Z ⟶ X) (z : Z) (j : L.ι), q z ∈ L.U j →
        gs q z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j)) (s.f fun _ => j) = gs q z (L.U j) (b.f j) := by
    have le : ∀ j, L.U j ≤ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j) := fun j y hy => Set.mem_iInter.2 fun _ => hy
    refine ⟨⟨fun j => resG _ (le j) (s.f fun _ => j), fun j i => fn_ext fun y hy => ?_⟩,
      fun Z q z j hj => (gs_res q z (le j) hj _).symm⟩
    refine ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le j) hy.1 _)).trans
      ((sec_trans s (𝟙 _) y (le j hy.1) (le i hy.2)).trans (Eq.trans ?_ (gs_mul (𝟙 _) y _ hy _ _).symm))
    refine congrArg₂ (· * ·) ?_ ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le i) hy.2 _)).symm
    refine Eq.trans ?_ ((gs_unit (𝟙 _) y _ hy _).trans (congrArg Units.val (map_zpow _ _ _))).symm
    refine congrArg Units.val ((Fin.prod_univ_one _).trans ?_)
    rw [Category.comp_id]
    rfl
  obtain ⟨b, hb⟩ := exists_pw_local
  exact ⟨KeyOnPol.ofPow b, fun Z r z J hJ =>
    (sval_of s r z J (fun _ => J r) fun _ => by rw [Category.comp_id]).trans (hb Z r z _ (hJ r))⟩

theorem exists_up {X : Scheme.{0}} {L : LB X} (t : L.Sec) : ∃ s : H0 L 1, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z)
    (J : (Z ⟶ X) → L.ι), Good L z J → sval s r z J = gs r z (L.U (J r)) (t.f (J r)) := by
  have exists_up_local : ∃ s : H0 L 1,
      ∀ (Z : Scheme.{0}) (q : Z ⟶ X) (z : Z) (j : L.ι), q z ∈ L.U j →
        gs q z (LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => j)) (s.f fun _ => j) = gs q z (L.U j) (t.f j) := by
    have le : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => 𝟙 X) j ≤ L.U (j 0) := fun j y hy => Set.mem_iInter.1 hy 0
    refine ⟨⟨fun j => resG X (le j) (t.f (j 0)), fun j i => fn_ext fun y hy => ?_⟩,
      fun Z q z j hj => gs_res q z (le _) (Set.mem_iInter.2 fun _ => hj) _⟩
    refine ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le j) hy.1 _)).trans (Eq.trans ?_ ((gs_mul (𝟙 X) y _ hy _ _).trans
      (congrArg₂ (· * ·) ((gs_unit (𝟙 X) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 X) y j i hy.1 hy.2)))
        ((gs_res (𝟙 X) y _ hy _).trans (gs_res (𝟙 X) y (le i) hy.2 _)))).symm)
    have hm : (𝟙 X) y ∈ L.U (j 0) ⊓ L.U (i 0) := ⟨le j hy.1, le i hy.2⟩
    have ht : gs (𝟙 X) y _ (t.f (j 0)) = (gm (𝟙 X) y _ (L.g (j 0) (i 0))).val * gs (𝟙 X) y _ (t.f (i 0)) :=
      (gs_res (𝟙 X) y _ hm _).symm.trans ((congrArg (gs (𝟙 X) y _) (t.compat (j 0) (i 0))).trans
        ((gs_mul (𝟙 X) y _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) y _ hm _) (gs_res (𝟙 X) y _ hm _))))
    rw [ht, Fin.prod_univ_one, Nat.cast_one, zpow_one, Category.id_comp]
  obtain ⟨s, hs⟩ := exists_up_local
  exact ⟨s, fun Z r z J hJ =>
    (sval_of s r z J (fun _ => J r) fun _ => by rw [Category.comp_id]).trans (hs Z r z _ (hJ r))⟩

theorem exists_generator_pull : Laws → ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (f : R →+* R') (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (Φ : P'.A.left ⟶ P.A.left) (w : LB.Iso P'.L (P.L.pull Φ)), IsGrpPullback P'.A P.A (spMap f) Φ → w.IsGen → ∀ th : H0 P.L 1, (∀ s : H0 P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal P.A.hom r) * th.f j) → ∃ th' : H0 P'.L 1, (∀ s : H0 P'.L 1, ∃ r : R', ∀ j, s.f j = resTop _ (scal P'.A.hom r) * th'.f j) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ P'.A.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι) (J' : (Z ⟶ P'.A.left) → P'.L.ι), Good P.L z J → Good P'.L z J' → sval th (r ≫ Φ) z J = (gw w r z (J (r ≫ Φ)) (J' r)).val * sval th' r z J' := by
  intro hL R R' _ _ _ _ f P P' Φ w hΦ hw th hth
  obtain ⟨b, hb, -⟩ := KeyOnPol.exists_generator hL.secBaseChange P
  obtain ⟨t, ht⟩ := exists_down th
  obtain ⟨β, hβ⟩ := exists_up b
  obtain ⟨a, ha⟩ := hth β
  have nz : ∀ y : Sp R, ∃ x : P.A.left, P.A.hom x = y ∧ x ∈ nonzeroLocus t := fun y => by
    obtain ⟨x, hx, hn⟩ := hb y
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hn
    obtain ⟨J, hJ, e⟩ := exists_good P.L P.isLB x (fun _ : PUnit => 𝟙 P.A.left) (fun _ => k) (fun _ _ _ => rfl)
      fun _ => hk
    obtain rfl : J (𝟙 _) = k := e PUnit.unit
    have h := IndivisibleSection.sval_of_secIsMul (p := P.A.hom) (a := a) (s := β) (t := th) ha (𝟙 _) x hJ
    rw [hβ _ _ x J hJ, ht _ _ x J hJ] at h
    exact ⟨x, hx, (mem_nonzeroLocus _ _).2 ⟨_, hk, isUnit_of_mul_isUnit_right (h ▸ u)⟩⟩
  obtain ⟨t', ht'⟩ := sec_pull_down ((isGen_iff w).1 hw) P.isLB P'.isLB t
  have nz' := SectionBaseChange.fibre_nonzero_of_pull P'.isLB ht' hΦ.1 nz
  obtain ⟨th', hth'⟩ := exists_up t'
  refine ⟨th', fun s => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · obtain ⟨σ, hσ⟩ := exists_down s
    obtain ⟨c, hc, -⟩ := SectionBaseChange.generates hL.secBaseChange P hΦ.1 P'.isLB ⟨w, hw⟩ t' nz' σ
    refine ⟨c, IndivisibleSection.secIsMul_of_sval P'.isLB fun y J hJ => ?_⟩
    rw [hσ _ _ y J hJ, hth' _ _ y J hJ]
    exact (sec_eq_iff _ _ _ _).1 hc _ y (hJ (𝟙 _))
  · rw [ht _ _ z J hJ, hth' _ _ z J' hJ']
    exact ht' Z r z _ _ (hJ (r ≫ Φ)) (hJ' r)

end GlobalTheory.GeneratorPull
