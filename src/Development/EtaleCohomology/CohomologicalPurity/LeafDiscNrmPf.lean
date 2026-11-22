module

public import Development.EtaleCohomology.CohomologicalPurity.LeafDiscPf
public import Development.EtaleCohomology.TateTwists.EtaleChainCochainExistsOfEvalData
public import Development.EtaleCohomology.KummerTheory.CupAWCutEv

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Cl.DiscNrmPf

def up {P : PSh} {U : Scheme.{0}} {p q : ℕ} (x : Sx (disc.obj P) p U) : Sx (disc.obj P) q U := x

theorem face_disc {P : PSh} {U : Scheme.{0}} {p : ℕ} (x : Sx (disc.obj P) (p + 1) U) (i : Fin (p + 2)) :
    ((disc.obj P).δ i).app (op U) x = up x := rfl

open LateralTheory.KummerTheory.AW in
theorem normal (R : Type) [CommRing R] (I : Cx R) (P : PSh) (n : ℤ) (α : Cocycle ((chains R).obj (disc.obj P)) I n) :
    ∃ β : Cochain ((chains R).obj (disc.obj P)) I (n - 1), ∀ p s h U y,
      ev (R := R) (α.1 - δ (n - 1) n β) (p + 1) s h U y = 0 := by
  have hα : δ n (n + 1) α.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2
  have hEval {k : ℤ} (γ : Cochain ((chains R).obj (disc.obj P)) I k) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + k = s) (U : Scheme.{0}) (x : Sx (disc.obj P) p U) :
      ev (R := R) γ p s h U x = Sec.map ((chainsXIso R (disc.obj P) p).inv ≫ γ.v _ _ h) (freeGen R P U x) := rfl
  have hD {k l : ℤ} (hkl : k + 1 = l) (γ : Cochain ((chains R).obj (disc.obj P)) I k)
      (U : Scheme.{0}) (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + k = s)
      (ht : -((p + 1 : ℕ) : ℤ) + l = t) (x : Sx (disc.obj P) (p + 1) U) :
      ev (R := R) (δ k l γ) (p + 1) t ht U x = Sec.map (I.d s t) (ev (R := R) γ (p + 1) s hs U x) +
        l.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          ev (R := R) γ p t (by omega) U (((disc.obj P).δ i).app (op U) x) := by
    rw [hEval, δ_v k l hkl γ _ _ ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add,
      Linear.comp_units_smul, reassoc_of% (LateralTheory.KummerTheory.chains_d R (disc.obj P) p),
      Preadditive.sum_comp, sec_map_add]
    congr 1
    rw [Units.smul_def, Units.smul_def, sec_map_zsmul, sec_map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Preadditive.zsmul_comp, sec_map_zsmul, hEval]
    congr 1
    exact congrArg (Sec.map ((chainsXIso R (disc.obj P) p).inv ≫ γ.v (-(p : ℤ)) t (by omega)))
      (map_freeGen ((disc.obj P).δ i) U x)
  let a (p : ℕ) (s : ℤ) (h : -(p : ℤ) + (n - 1) = s) (U : Scheme.{0}) (x : Sx (disc.obj P) p U) : Sec (I.X s) U :=
    if Odd p then n.negOnePow • ev (R := R) α.1 (p + 1) s (by push_cast; omega) U (up x) else 0
  have hex (p : ℕ) (s : ℤ) (h : -(p : ℤ) + (n - 1) = s) :
      ∃ φ : (free R).obj P ⟶ I.X s, ∀ U x, Sec.map φ (freeGen R P U x) = a p s h U x :=
    LateralTheory.EtaleFoundations.EvMkPf.free_hom_exists R P (I.X s) (a p s h) (by
      intro V U g x
      dsimp only [a]
      split_ifs
      · rw [Units.smul_def, Units.smul_def]
        refine (map_zsmul ((I.X s).obj.map g.op).hom _ _).trans ?_
        congr 1
        change Sec.res g (ev (R := R) α.1 (p + 1) s _ U (up x)) =
          ev (R := R) α.1 (p + 1) s _ V (up (P.map g.op x))
        rw [hEval, hEval, sec_map_res, freeGen_res]
        rfl
      · exact map_zero _)
  choose φ hφ using hex
  let f (p : ℕ) (s : ℤ) (h : -(p : ℤ) + (n - 1) = s) : ((chains R).obj (disc.obj P)).X (-(p : ℤ)) ⟶ I.X s :=
    (chainsXIso R (disc.obj P) p).hom ≫ φ p s h
  let β : Cochain ((chains R).obj (disc.obj P)) I (n - 1) := Cochain.mk (fun i j hij =>
    if hi : 0 ≤ -i then
      (((chains R).obj (disc.obj P)).XIsoOfEq (show i = -(((-i).toNat : ℕ) : ℤ) by omega)).hom ≫
        f (-i).toNat j (by omega)
    else 0)
  have hβ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + (n - 1) = s) (U : Scheme.{0}) (x : Sx (disc.obj P) p U) :
      ev (R := R) β p s h U x = a p s h U x := by
    have hComponent (q : ℕ) (hq : q = p) (e : -(p : ℤ) = -(q : ℤ)) (h' : -(q : ℤ) + (n - 1) = s) :
        (((chains R).obj (disc.obj P)).XIsoOfEq e).hom ≫ f q s h' = f p s h := by
      subst q
      simp
    have hv : β.v (-(p : ℤ)) s h = f p s h := by
      simp only [β, Cochain.mk_v]
      rw [dite_eq_left (by omega)]
      exact hComponent _ (by omega) _ _
    rw [hEval, hv]
    simp only [f, Iso.inv_hom_id_assoc]
    exact hφ p s h U x
  refine ⟨β, ?_⟩
  intro p s h U y
  have hSub : ev (R := R) (α.1 - δ (n - 1) n β) (p + 1) s h U y =
      ev (R := R) α.1 (p + 1) s h U y - ev (R := R) (δ (n - 1) n β) (p + 1) s h U y := by
    rw [hEval, hEval, hEval, Cochain.sub_v, Preadditive.comp_sub]
    exact map_sub (AddMonoidHom.mk' (fun m => Sec.map m (freeGen R P U y)) (fun _ _ => sec_map_add _ _ _)) _ _
  rw [hSub, sub_eq_zero, hD (by omega) β U p (s - 1) s (by push_cast at h ⊢; omega) h y]
  simp only [face_disc, hβ, a]
  rcases Nat.even_or_odd p with hp | hp
  · have hp1 : Odd (p + 1) := hp.add_one
    have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
    simp only [hp1, hp0, ite_true, ite_false, smul_zero, Finset.sum_const_zero, add_zero]
    have hc := hD rfl α.1 U (p + 1) (s - 1) s (by push_cast at h ⊢; omega)
      (by push_cast at h ⊢; omega) (up y)
    rw [hα] at hc
    have hZero : ev (R := R) (0 : Cochain ((chains R).obj (disc.obj P)) I (n + 1))
        (p + 1 + 1) s (by push_cast at h ⊢; omega) U (up y) = 0 := by simp [ev]
    rw [hZero] at hc
    simp only [face_disc] at hc
    rw [← Finset.sum_smul, LateralTheory.KummerTheory.altsum] at hc
    have he : ¬ Even (p + 1 + 2) := by
      rw [Nat.not_even_iff_odd]; exact hp1.add_even even_two
    simp only [he, ite_false, one_smul] at hc
    rw [Int.negOnePow_succ, Units.neg_smul] at hc
    have key := add_neg_eq_zero.1 hc.symm
    rw [Units.smul_def]
    refine Eq.trans ?_ (map_zsmul ((I.d (s - 1) s).hom.app (op U)).hom _ _).symm
    rw [show (ModuleCat.Hom.hom ((I.d (s - 1) s).hom.app (op U))) (ev α.1 (p + 1 + 1) (s - 1) (by push_cast at h ⊢; omega) U (up y))
        = n.negOnePow • ev α.1 (p + 1) s (by push_cast at h ⊢; omega) U (up (up y)) from key]
    rw [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
    rfl
  · have hp1 : ¬ Odd (p + 1) := Nat.not_odd_iff_even.mpr hp.add_one
    simp only [hp1, hp, ite_true, ite_false, map_zero, zero_add]
    rw [← Finset.sum_smul, LateralTheory.KummerTheory.altsum]
    have he : ¬ Even (p + 2) := by
      rw [Nat.not_even_iff_odd]; exact hp.add_even even_two
    simp only [he, ite_false, one_smul, smul_smul, Int.units_mul_self]
    rfl

end LateralTheory.CohomologicalPurity.Cl.DiscNrmPf

namespace LateralTheory.CohomologicalPurity.Cl

open DiscNrmPf LateralTheory.KummerTheory.AW in
theorem etale_discrete_presheaf_cocycle_normalization_holds : LeafDiscNrm := by
  intro R _ K n P z
  obtain ⟨β, hβ⟩ := normal R K P n z
  refine ⟨(chainsXIso R (disc.obj P) 0).inv ≫ (z.1 - δ (n - 1) n β).v (-((0 : ℕ) : ℤ)) n (by omega), β, ?_⟩
  rw [← sub_eq_iff_eq_add]
  have hExt (a b : Cochain ((chains R).obj (disc.obj P)) K n)
      (hab : ∀ p s h U x, ev (R := R) a p s h U x = ev (R := R) b p s h U x) : a = b := by
    ext i j hij : 1
    by_cases hi : 0 < i
    · exact (isZero_pos (R := R) (disc.obj P) i hi).eq_of_src _ _
    · obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R (disc.obj P) p).inv]
      exact free_ext _ _ (fun U x => hab p j hij U x)
  apply hExt
  intro p s h U x
  rcases p with _ | p
  · obtain rfl : s = n := by omega
    simp only [ev, Cochain.single_v, Iso.inv_hom_id_assoc]
  · rw [hβ]
    simp only [ev]
    rw [Cochain.single_v_eq_zero _ _ _ _ _ (by push_cast; omega), comp_zero]
    rfl

theorem LeafDisc_of' : LeafDisc := LeafDisc_of etale_discrete_presheaf_cocycle_normalization_holds

end LateralTheory.CohomologicalPurity.Cl
