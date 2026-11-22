module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.HMapSumZsmulAdd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.PtHCompPermMapOfEquivariant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.FaceStdSeqGLConjugateCommutingStab

@[expose] public section

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

theorem altSum_neg_one (p : ℕ) : (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ)) = if Even p then 1 else 0 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih]
    rcases Nat.even_or_odd p with hp | hp
    · have h2 : ¬ Even (p + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hp
      rw [if_pos hp, if_neg h2, pow_succ, hp.neg_one_pow]
      norm_num
    · have h2 : Even (p + 1) := by rw [Nat.even_add_one]; exact Nat.not_even_iff_odd.mpr hp
      rw [if_neg (Nat.not_even_iff_odd.mpr hp), if_pos h2, pow_succ, hp.neg_one_pow]
      norm_num

theorem stab_comp_stab (R : Type) [CommRing R] (a b c : ℕ) (hab : a ≤ b) (hbc : b ≤ c) (hac : a ≤ c) :
    (stab R b c hbc).comp (stab R a b hab) = stab R a c hac := by
  ext g i j
  simp only [MonoidHom.comp_apply, stab, Units.coe_map, padHom, MonoidHom.coe_mk, OneHom.coe_mk, padMat, Matrix.of_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> simp_all [Fin.ext_iff] <;> omega

theorem ptH_comp_hMap_splitD : ∀ (R : Type) [CommRing R] (n p q : ℕ) (h : p + 1 ≤ n) (h₁ : ∀ x, stab R (n - (p + 1)) n (Nat.sub_le _ _) x • stdSeq R n (p + 1) h = stdSeq R n (p + 1) h) (h₀ : ∀ x, stab R (n - p) n (Nat.sub_le _ _) x • stdSeq R n p (by omega) = stdSeq R n p (by omega)), ptH (k := ℤ) (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stdSeq R n (p + 1) h) h₁ q ≫ hMap (splitD R n p) q = if Even p then grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ ptH (k := ℤ) (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q else 0 := by
  intro R _ n p q h h₁ h₀
  have hσ : (stab R (n - p) n (Nat.sub_le _ _)).comp (stab R (n - (p + 1)) (n - p) (by omega)) =
      stab R (n - (p + 1)) n (Nat.sub_le _ _) := stab_comp_stab R _ _ _ _ _ _
  have hpoint : ∀ (G H H' X Y : Type) [Group G] [Group H] [Group H']
      [MulAction G X] [MulAction G Y] (φ : H →* G) (φ' : H' →* G) (σ : H' →* H)
      (x : X) (hx : ∀ h, φ' h • x = x) (y : Y) (hy : ∀ h, φ h • y = y)
      (f : X → Y) (hf : ∀ (g : G) z, f (g • z) = g • f z) (g : G),
      φ.comp σ = φ' → g • f x = y → (∀ h, g * φ' h = φ' h * g) → ∀ n : ℕ,
      ptH (k := ℤ) φ' x hx n ≫ hMap (permMap f hf (Rep.trivial ℤ G ℤ)) n =
        groupHomology.map (A := Rep.trivial ℤ H' ℤ) (B := Rep.trivial ℤ H ℤ)
          σ (𝟙 (Rep.trivial ℤ H' ℤ)) n ≫ ptH (k := ℤ) φ y hy n := by
    intro G H H' X Y _ _ _ _ _ φ φ' σ x hx y hy f hf g hcomp hgy hc n
    subst hcomp
    have hfx : ∀ h, (φ.comp σ) h • f x = f x := fun h => by rw [← hf, hx]
    have hy' : ∀ h, (φ.comp σ) h • y = y := fun h => hy (σ h)
    have h1 := groupHomology.map_comp (A := Rep.trivial ℤ H' ℤ)
      (B := perm (k := ℤ) (G := G) X) (C := perm (k := ℤ) (G := G) Y)
      (φ.comp σ) (MonoidHom.id G) (ptMap (φ.comp σ) x hx (Rep.trivial ℤ G ℤ))
      (permMap f hf (Rep.trivial ℤ G ℤ)) n
    have hmor : (ptMap (φ.comp σ) x hx (Rep.trivial ℤ G ℤ) ≫
        (Rep.resFunctor (φ.comp σ)).map (permMap f hf (Rep.trivial ℤ G ℤ)) :
          Rep.trivial ℤ H' ℤ ⟶ Rep.res (φ.comp σ) (perm (k := ℤ) (G := G) Y)) =
        ptMap (φ.comp σ) (f x) hfx (Rep.trivial ℤ G ℤ) := by
      ext a
      change (Finsupp.mapDomain f (Finsupp.single x (1 : ℤ))) a = (Finsupp.single (f x) (1 : ℤ)) a
      rw [Finsupp.mapDomain_single]
    have hL : ptH (k := ℤ) (φ.comp σ) x hx n ≫ hMap (permMap f hf (Rep.trivial ℤ G ℤ)) n =
        groupHomology.map (φ.comp σ) (ptMap (φ.comp σ) (f x) hfx (Rep.trivial ℤ G ℤ)) n :=
      h1.symm.trans (congrArg (fun u => groupHomology.map (φ.comp σ) u n) hmor)
    have h2 := groupHomology.map_comp (A := Rep.trivial ℤ H' ℤ) (B := Rep.trivial ℤ H ℤ)
      (C := perm (k := ℤ) (G := G) Y)
      σ φ (𝟙 (Rep.trivial ℤ H' ℤ)) (ptMap φ y hy (Rep.trivial ℤ G ℤ)) n
    have hmor2 : (𝟙 (Rep.trivial ℤ H' ℤ) ≫ (Rep.resFunctor σ).map (ptMap φ y hy (Rep.trivial ℤ G ℤ)) :
          Rep.trivial ℤ H' ℤ ⟶ Rep.res (φ.comp σ) (perm (k := ℤ) (G := G) Y)) =
        ptMap (φ.comp σ) y hy' (Rep.trivial ℤ G ℤ) := by
      ext a
      rfl
    have hR : groupHomology.map (A := Rep.trivial ℤ H' ℤ) (B := Rep.trivial ℤ H ℤ) σ
        (𝟙 (Rep.trivial ℤ H' ℤ)) n ≫ ptH (k := ℤ) φ y hy n =
        groupHomology.map (φ.comp σ) (ptMap (φ.comp σ) y hy' (Rep.trivial ℤ G ℤ)) n :=
      h2.symm.trans (congrArg (fun u => groupHomology.map (φ.comp σ) u n) hmor2)
    rw [hL, hR]
    symm
    refine groupHomology_map_conj ℤ G H' (Rep.trivial ℤ H' ℤ) (perm (k := ℤ) (G := G) Y)
      (φ.comp σ) (φ.comp σ)
      (ptMap (φ.comp σ) (f x) hfx (Rep.trivial ℤ G ℤ)) (ptMap (φ.comp σ) y hy' (Rep.trivial ℤ G ℤ)) g
      (fun h => by rw [hc h, mul_inv_cancel_right]) (fun a => ?_) n
    subst hgy
    change Finsupp.single (g • f x) a =
      Finsupp.mapDomain (fun z => g • z) (Finsupp.mapRange id rfl (Finsupp.single (f x) a))
    rw [Finsupp.mapRange_id, Finsupp.mapDomain_single]
  unfold splitD
  rw [(GlobalTheory.T.hMap_sum_zsmul_add ℤ _ _ _ q).2.2.2 _ Finset.univ, Preadditive.comp_sum]
  rw [Finset.sum_congr rfl (g := fun i : Fin (p + 1) => ((-1 : ℤ) ^ (i : ℕ)) •
      (grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫
        ptH (k := ℤ) (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q)) ?_]
  · rw [← Finset.sum_smul, altSum_neg_one]
    split_ifs <;> simp
  · intro i _
    rw [(GlobalTheory.T.hMap_sum_zsmul_add ℤ _ _ _ q).2.2.1, Preadditive.comp_zsmul]
    obtain ⟨g, hg, hc⟩ := GlobalTheory.T.face_stdSeq_GL_conjugate_commuting_stab R n p h i
    have hface := hpoint _ _ _ _ _ (stab R (n - p) n (Nat.sub_le _ _))
      (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stab R (n - (p + 1)) (n - p) (by omega))
      _ h₁ _ h₀ (face R n p i) (face_smul R n p i) g hσ hg hc q
    exact congrArg (fun m => ((-1 : ℤ) ^ (i : ℕ)) • m) hface

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
theorem _root_.GlobalTheory.T.standardSeqPoint_comp_splitSeqDifferential : ∀ (R : Type) [CommRing R] (n p q : ℕ) (h : p + 1 ≤ n) (h₁ : ∀ x, stab R (n - (p + 1)) n (Nat.sub_le _ _) x • stdSeq R n (p + 1) h = stdSeq R n (p + 1) h) (h₀ : ∀ x, stab R (n - p) n (Nat.sub_le _ _) x • stdSeq R n p (by omega) = stdSeq R n p (by omega)), ptH (k := ℤ) (stab R (n - (p + 1)) n (Nat.sub_le _ _)) (stdSeq R n (p + 1) h) h₁ q ≫ hMap (splitD R n p) q = if Even p then grpHMap (stab R (n - (p + 1)) (n - p) (by omega)) q ≫ ptH (k := ℤ) (stab R (n - p) n (Nat.sub_le _ _)) (stdSeq R n p (by omega)) h₀ q else 0 := by
  first
  | exact @GlobalTheory.HomStab.ptH_comp_hMap_splitD
  | exact @GlobalTheory.HomStab.stab_comp_stab
  | exact @GlobalTheory.HomStab.altSum_neg_one
end
