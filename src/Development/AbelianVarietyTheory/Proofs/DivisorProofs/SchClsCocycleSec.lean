module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SchCls

theorem sum_neg_one_pow (p : ℕ) : ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) = if Even p then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i)]
  induction p with
  | zero => simp [Finset.sum_range_succ]
  | succ q ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd q with h | h
    · have h2 : Even (q + 1 + 1) := by rw [add_assoc]; exact h.add even_two
      simp [h, Nat.even_add_one, h2.neg_one_pow]
    · have h2 : Odd (q + 1 + 1) := by rw [add_assoc]; exact h.add_even even_two
      have h3 : Even (q + 1) := h.add_one
      simp [h3, h2.neg_one_pow, Nat.not_even_iff_odd.mpr h]

variable {R : Type} [CommRing R]

theorem face_sch {X U : Scheme.{0}} {p : ℕ} (x : Sx (sch.obj X) (p + 1) U) (i : Fin (p + 2)) : x.face i = x := rfl

theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.res f z) = Sec.res (g ≫ f) z := by
  simp [Sec.res]

theorem map_id' {F : Shv R} {U : Scheme.{0}} (y : Sec F U) : Sec.map (𝟙 F) y = y := rfl

theorem map_units_smul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (u : ℤˣ) (y : Sec F U) :
    Sec.map φ (u • y) = u • Sec.map φ y := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem res_units_smul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (u : ℤˣ) (y : Sec F U) :
    Sec.res g (u • y) = u • Sec.res g y := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

theorem ev_δ_sch {X : Scheme.{0}} {I : Cx R} {n k : ℤ} (hk : n + 1 = k)
    (α : Cochain ((chains R).obj (sch.obj X)) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
    (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + k = t) (x : Sx (sch.obj X) (p + 1) U) :
    ev (δ n k α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
      (if Even p then 0 else k.negOnePow • ev α p t (by omega) U x) := by
  have hsum :
      ev (δ n k α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
        k.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U x := by
    change Sec.map ((chainsXIso R (sch.obj X) (p + 1)).inv ≫ (δ n k α).v _ _ ht)
      (freeGen R _ U x) = _
    rw [δ_v n k hk α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add,
      Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj (sch.obj X)).d _ _),
      CupSpec.chains_d, Category.assoc, Preadditive.sum_comp]
    refine (map_add (CupSpec.mapHom _ _ (freeGen R _ U x)) _ _).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zsmul, map_sum, Units.smul_def]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map ((chainsXIso R (sch.obj X) p).inv ≫ α.v _ _ _)
      (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [CupSpec.freeGen_map]
    rfl
  rw [hsum]
  rw [← Finset.sum_smul, sum_neg_one_pow]
  split_ifs <;> simp

end GlobalTheory.EtC.SchCls

namespace GlobalTheory.EtC


open GlobalTheory.EtC.SchCls in
theorem sch_cls_cocycle_sec : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n k : ℤ),
    m + 1 = n → n + 1 = k →
      (∀ z : Sec (I.X n) X, Sec.map (I.d n k) z = 0 →
        ∃ α : Cocycle ((chains R).obj (sch.obj X)) I n,
          (∀ (U : Scheme.{0}) (x : U ⟶ X), ev α.1 0 n (by simp) U x = Sec.res x z) ∧
            ∀ (p : ℕ) s h U x, ev α.1 (p + 1) s h U x = 0) ∧
      ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n,
        Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 ∧
          (CohomologyClass.mk α = 0 ↔
            ∃ y : Sec (I.X m) X, Sec.map (I.d m n) y = ev α.1 0 n (by simp) X (𝟙 X)) := by
  intro R _ X I m n k hmn hnk
  have ev_exists {j : ℤ}
      (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + j = s →
        ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U)
      (ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
        Sec.res g (a p s h U x) = a p s h V (x.res g)) :
      ∃ α : Cochain ((chains R).obj (sch.obj X)) I j,
        ∀ p s h U x, ev α p s h U x = a p s h U x := by
    have key : ∀ (i s : ℤ) (h : i + j = s),
        ∃ φ : ((chains R).obj (sch.obj X)).X i ⟶ I.X s,
          ∀ (p : ℕ) (hp : i = -(p : ℤ)) U x,
            Sec.map ((chainsXIso R (sch.obj X) p).inv ≫
              eqToHom (congrArg ((chains R).obj (sch.obj X)).X hp.symm) ≫ φ) (freeGen R _ U x) =
                a p s (hp ▸ h) U x := by
      intro i s h
      by_cases hi : i ≤ 0
      · obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = -(q : ℤ) := ⟨(-i).toNat, by omega⟩
        obtain ⟨φ, hφ⟩ := CupSpec.free_exists (R := R) _ _ (a q s h) (ha q s h)
        refine ⟨(chainsXIso R (sch.obj X) q).hom ≫ φ, fun p hp U x => ?_⟩
        obtain rfl : q = p := by omega
        rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
        exact hφ U x
      · exact ⟨0, fun p hp => by omega⟩
    choose φ hφ using key
    refine ⟨Cochain.mk φ, fun p s h U x => ?_⟩
    have heval := hφ _ _ h p rfl U x
    rw [eqToHom_refl, Category.id_comp] at heval
    exact heval
  have ev_δ_zero {i j : ℤ} (hij : i + 1 = j)
      (a : Cochain ((chains R).obj (sch.obj X)) I i) (U : Scheme.{0}) (s t : ℤ)
      (hs : -((0 : ℕ) : ℤ) + i = s) (ht : -((0 : ℕ) : ℤ) + j = t) (x : Sx (sch.obj X) 0 U) :
      ev (δ i j a) 0 t ht U x = Sec.map (I.d s t) (ev a 0 s hs U x) := by
    change Sec.map ((chainsXIso R (sch.obj X) 0).inv ≫ (δ i j a).v _ _ ht) (freeGen R _ U x) = _
    rw [δ_v i j hij a _ t ht s 1 (by omega) (by simp),
      (CupSpec.isZero_chains (R := R) (sch.obj X) 1 one_pos).eq_of_tgt
        (((chains R).obj (sch.obj X)).d _ 1) 0, zero_comp, smul_zero, add_zero]
    rfl
  have ev_zero {j : ℤ} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + j = s)
      (U : Scheme.{0}) (x : Sx (sch.obj X) p U) :
      ev (0 : Cochain ((chains R).obj (sch.obj X)) I j) p s h U x = 0 := by
    change Sec.map ((chainsXIso R (sch.obj X) p).inv ≫
      (0 : Cochain ((chains R).obj (sch.obj X)) I j).v _ _ h) (freeGen R _ U x) = 0
    rw [Cochain.zero_v, comp_zero]
    rfl
  have ev_res {j : ℤ} (a : Cochain ((chains R).obj (sch.obj X)) I j)
      (p : ℕ) (s : ℤ) (h : -(p : ℤ) + j = s) {V U : Scheme.{0}}
      (g : V ⟶ U) (x : Sx (sch.obj X) p U) :
      Sec.res g (ev a p s h U x) = ev a p s h V (x.res g) := by
    change Sec.res g (Sec.map ((chainsXIso R (sch.obj X) p).inv ≫ a.v _ _ h) (freeGen R _ U x)) = _
    rw [CupSpec.map_res, CupSpec.freeGen_res]
    rfl
  have ev_ext {j : ℤ} (a b : Cochain ((chains R).obj (sch.obj X)) I j)
      (h : ∀ p s h U x, ev a p s h U x = ev b p s h U x) : a = b := by
    ext p s hs : 1
    by_cases hp : p ≤ 0
    · obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = -(q : ℤ) := ⟨(-p).toNat, by omega⟩
      rw [← cancel_epi (chainsXIso R (sch.obj X) q).inv]
      exact CupSpec.free_ext _ _ (fun U x => h q s hs U x)
    · exact (CupSpec.isZero_chains (R := R) (sch.obj X) p (by omega)).eq_of_src _ _
  refine ⟨fun z hz => ?_, fun α => ?_⟩
  · obtain ⟨a, ha⟩ := ev_exists (j := n)
      (fun p s h U x => if hp : p = 0 then
        Sec.map (I.XIsoOfEq (show n = s by omega)).hom (Sec.res (x : U ⟶ X) z) else 0)
      (by
        intro p s h V U g x
        by_cases hp : p = 0
        · subst hp
          simp only [dite_eq_left]
          erw [CupSpec.map_res, SchCls.res_comp]
          rfl
        · simp only [dite_eq_right hp]
          exact map_zero _)
    have hc : δ n k a = 0 := by
      refine ev_ext _ _ fun p t ht U x => ?_
      erw [ev_zero]
      cases p with
      | zero =>
        have hkt : k = t := by omega
        subst hkt
        erw [ev_δ_zero hnk a U n k (by simp) ht x, ha]
        simp only [dite_eq_left, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, SchCls.map_id']
        erw [← CupSpec.map_res, hz]
        exact map_zero _
      | succ p =>
        erw [SchCls.ev_δ_sch hnk a U p (-((p + 1 : ℕ) : ℤ) + n) t (by omega) ht x, ha, ha]
        simp only [Nat.add_one_ne_zero, dite_eq_right, not_false_eq_true, map_zero, zero_add]
        split_ifs with he hp0
        · rfl
        · exact absurd (hp0 ▸ (⟨0, rfl⟩ : Even 0)) he
        · exact smul_zero _
    refine ⟨Cocycle.mk a k hnk hc, fun U x => ?_, fun p s h U x => ?_⟩
    · change ev a 0 n _ U x = _
      erw [ha]
      simp only [dite_eq_left, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, SchCls.map_id']
    · change ev a (p + 1) s h U x = 0
      erw [ha]
      simp
  · have hδ := Cocycle.δ_eq_zero α k
    refine ⟨?_, ?_⟩
    · have h0 := ev_δ_zero hnk α.1 X n k (by simp) (by simp) (𝟙 X)
      erw [hδ, ev_zero] at h0
      exact h0.symm
    erw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α m hmn]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev β 0 m (by simp) X (𝟙 X), ?_⟩
      erw [← hβ, ev_δ_zero hmn β X m n (by simp) (by simp)]
    · rintro ⟨y, hy⟩
      obtain ⟨b, hb⟩ := ev_exists (j := m)
        (fun p s h U x => if hp : p = 0 then
          Sec.map (I.XIsoOfEq (show m = s by omega)).hom (Sec.res (x : U ⟶ X) y)
          else if Even p then 0 else (-k.negOnePow) • ev α.1 (p + 1) s (by omega) U x)
        (by
          intro p s h V U g x
          by_cases hp : p = 0
          · subst hp
            simp only [dite_eq_left]
            erw [CupSpec.map_res, SchCls.res_comp]
            rfl
          · simp only [dite_eq_right hp]
            split_ifs
            · exact map_zero _
            · erw [SchCls.res_units_smul, ev_res]
              rfl)
      refine ⟨b, ev_ext _ _ fun p t ht U x => ?_⟩
      cases p with
      | zero =>
        have hnt : n = t := by omega
        subst hnt
        erw [ev_δ_zero hmn b U m n (by simp) ht x, hb]
        simp only [dite_eq_left, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, SchCls.map_id']
        erw [← CupSpec.map_res, hy, ev_res]
        congr 1
      | succ p =>
        erw [SchCls.ev_δ_sch hmn b U p (-((p + 1 : ℕ) : ℤ) + m) t (by omega) ht x, hb, hb]
        have hc := SchCls.ev_δ_sch hnk α.1 U (p + 1) (-((p + 1 : ℕ) : ℤ) + m) t (by omega) (by omega) x
        erw [hδ, ev_zero] at hc
        rcases Nat.even_or_odd p with he | ho
        · have hne : ¬ Even (p + 1) := Nat.not_even_iff_odd.mpr he.add_one
          simp only [Nat.add_one_ne_zero, dite_eq_right, not_false_eq_true, hne, ite_false, ite_eq_left he,
            add_zero] at hc ⊢
          erw [SchCls.map_units_smul, eq_neg_of_add_eq_zero_left hc.symm, smul_neg, smul_smul]
          simp [Int.units_mul_self]
        · have hne : ¬ Even p := Nat.not_even_iff_odd.mpr ho
          have hp0 : p ≠ 0 := fun h => hne (h ▸ (⟨0, rfl⟩ : Even 0))
          have hev : Even (p + 1) := ho.add_one
          simp only [Nat.add_one_ne_zero, dite_eq_right, not_false_eq_true, hev, ite_true, hne, ite_false,
            dite_eq_right hp0, map_zero, zero_add]
          have hkn : k.negOnePow = -n.negOnePow := by rw [← hnk, Int.negOnePow_succ]
          erw [hkn, neg_neg, smul_smul, Int.units_mul_self, one_smul]

end GlobalTheory.EtC
