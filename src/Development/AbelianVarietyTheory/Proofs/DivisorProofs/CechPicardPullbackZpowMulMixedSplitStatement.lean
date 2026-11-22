module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowMulMixedSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiMapFst
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPullOfRigOfSym
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (x y : T ⟶ A) (m n a b : ℤ), a • GlobalTheory.CechPic.pull (x ^ m * y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m * y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL) = (a • GlobalTheory.CechPic.pull (x ^ m).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((x ^ m)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + (a • GlobalTheory.CechPic.pull (y ^ n).left (GlobalTheory.CechPic.cls L hL) + b • GlobalTheory.CechPic.pull ((y ^ n)⁻¹).left (GlobalTheory.CechPic.cls L hL)) + ((a + b) * (m * n)) • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x y := by
  intro K _ A _ hA L hL T x y m n a b
  have : IsCommMonObj A := hA.comm
  have hΘ : ∃ t : LB.Gen (Theta A L), t.IsGen :=
    GlobalTheory.SymMulPull.hasGen_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have lam_zpow_left (x z : T ⟶ A) (n : ℤ) :
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ^ n) z =
        n • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x z := by
    open GlobalTheory.CechPic in
    cases n with
    | ofNat k =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, natCast_zsmul]
      exact lam_pow_left hL hΘ x z k
    | negSucc k =>
      have h := lam_mul_left hL hΘ (x ^ (k + 1)) (x ^ (k + 1))⁻¹ z
      rw [mul_inv_cancel, lam_one_left, lam_pow_left hL hΘ] at h
      rw [zpow_negSucc, negSucc_zsmul]
      exact eq_neg_of_add_eq_zero_right h.symm
  have lam_zpow_zpow (x y : T ⟶ A) (m n : ℤ) :
      GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) (x ^ m) (y ^ n) =
        (m * n) • GlobalTheory.CechPic.lam (GlobalTheory.CechPic.cls L hL) x y := by
    rw [lam_zpow_left, GlobalTheory.CechPic.lam_comm, lam_zpow_left,
      GlobalTheory.CechPic.lam_comm, smul_smul]
  have pull_one_eq_zero (c : GlobalTheory.CechPic.Pic A.left) :
      GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0 := by
    change GlobalTheory.CechPic.pull ((toUnit T).left ≫ (η : 𝟙_ (Over (Sp K)) ⟶ A).left) c = 0
    rw [GlobalTheory.CechPic.pull_comp, GlobalTheory.AmpleStabFinite.pull_spec_local (K := K) _ c, map_zero]
  have key : ∀ (c : GlobalTheory.CechPic.Pic A.left) (u v : T ⟶ A),
      GlobalTheory.CechPic.pull (u * v).left c = GlobalTheory.CechPic.pull u.left c +
        GlobalTheory.CechPic.pull v.left c + GlobalTheory.CechPic.lam c u v := by
    intro c u v
    unfold GlobalTheory.CechPic.lam
    rw [pull_one_eq_zero]
    abel
  rw [mul_inv, key, key, ← zpow_neg, ← zpow_neg, lam_zpow_zpow, lam_zpow_zpow, neg_mul_neg]
  module
