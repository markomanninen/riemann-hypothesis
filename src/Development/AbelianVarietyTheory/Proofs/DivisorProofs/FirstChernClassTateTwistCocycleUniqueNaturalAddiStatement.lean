module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddi
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

open GlobalTheory.EtC.ClsSpec in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstChernClassTateTwist_cocycle_unique_natural_additive :
    ∀ (q : ℕ) [NeZero q],
      (∀ {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E →
        ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2,
          CohomologyClass.mk γ = c1 q L ∧
          (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) γ.1 0 2 (by simp) U x = 0) ∧
          (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
            ev (R := ZMod q) γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
          ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ),
            v ^ q = lineUnit L (x.sub 0 1 (by omega)) → w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
            ev (R := ZMod q) γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) ∧
      (∀ {E E' : Spc} (f : E ⟶ E') (L : E' ⟶ ofCat (glCat 1)), Inv q E' →
        pull _ f _ _ (c1 q L) = c1 q (f ≫ L)) ∧
      ∀ {E : Spc} (L M N : E ⟶ ofCat (glCat 1)), Inv q E →
        (∀ (U : Scheme.{0}) (x : Sx E 1 U), lineUnit N x = lineUnit L x * lineUnit M x) →
        c1 q N = c1 q L + c1 q M := by
  intro q _
  refine ⟨?_, fun f L hE => ChernSpec.firstChernClassTateTwist_pullback q f L hE,
    fun L M N hE hN => ChernSpec.isOneCochain_add q L M N hE hN⟩
  have exists_single {E : Spc} {I : Cx (ZMod q)} {n : ℤ} (p₀ : ℕ) (s₀ : ℤ) (h₀ : -(p₀ : ℤ) + n = s₀)
      (b : ∀ U : Scheme.{0}, Sx E p₀ U → Sec (I.X s₀) U)
      (hb : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p₀ U), Sec.res g (b U x) = b V (x.res g)) :
      ∃ α : Cochain ((chains (ZMod q)).obj E) I n, (∀ U x, ev (R := ZMod q) α p₀ s₀ h₀ U x = b U x) ∧
        ∀ p s h U x, p ≠ p₀ → ev (R := ZMod q) α p s h U x = 0 := by
    subst h₀
    obtain ⟨α, hα⟩ := exists_cochain_ev_eq_of_natural (ZMod q) (E := E) (I := I) (n := n)
      (fun p s h U x => if hp : p = p₀ then (by subst hp; subst h; exact b U x) else 0) (by
        intro p s h V U g x
        by_cases hp : p = p₀
        · subst hp; subst h
          simp only [dite_eq_left]
          exact hb V U g x
        · simp only [dite_eq_right hp]
          exact map_zero _)
    refine ⟨α, fun U x => ?_, fun p s h U x hp => ?_⟩
    · rw [hα]
      simp only [dite_eq_left]
    · rw [hα]
      simp only [dite_eq_right hp]
  have differential_eq_zero {E : Spc} {I : Cx (ZMod q)} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains (ZMod q)).obj E) I n)
      (h₀ : ∀ (U : Scheme.{0}) (x : Sx E 0 U), Sec.map (I.d n m) (ev (R := ZMod q) α 0 n (by simp) U x) = 0)
      (h₁ : ∀ (U : Scheme.{0}) (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -(p : ℤ) + n = t) (x : Sx E (p + 1) U),
        Sec.map (I.d s t) (ev (R := ZMod q) α (p + 1) s hs U x) +
          m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev (R := ZMod q) α p t ht U (x.face i) = 0) : δ n m α = 0 := by
    refine CupSpec.ev_ext _ _ fun p t ht U x => ?_
    rw [CupSpec.ev_zero]
    cases p with
    | zero =>
      obtain rfl : m = t := by simpa using ht
      exact (CupSpec.ev_δ_zero hm α U n m (by simp) (by simp) x).trans (h₀ U x)
    | succ p => exact (CupSpec.ev_δ_succ hm α U p _ t rfl ht x).trans (h₁ U p _ t rfl _ x)
  have exists_cocycle {t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U} (ht : IsKum q t)
      {E : Spc} (hE : Inv q E) (L : E ⟶ ofCat (glCat 1)) :
      ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2,
      (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) γ.1 0 2 (by simp) U x = 0) ∧
      (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
        ev (R := ZMod q) γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (t U v)) ∧
      ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.face 2) →
        w ^ q = lineUnit L (x.face 0) →
        ev (R := ZMod q) γ.1 2 0 (by simp) U x = t U v + t U w - t U (v * w) := by
    have hq₁ : ∀ (U : Scheme.{0}) (_ : Sx E 1 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hE U ⟨x.face 0⟩
    have hq₂ : ∀ (U : Scheme.{0}) (_ : Sx E 2 U), IsUnit (q : Γ(U, ⊤)) := fun U x => hq₁ U (x.face 0)
    have hf : ∀ (i : Fin 3) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E 2 U),
        lineUnit L ((x.res g).face i) = umap g (lineUnit L (x.face i)) := fun i _ _ g x => ChernSpec.lineUnit_face_res L g x i
    obtain ⟨b, hb, hd, hv⟩ := exists_d_family ht hq₁ (fun U x => lineUnit L x) (fun V U g x => lineUnit_res L g x)
    obtain ⟨e, he, hw⟩ := exists_two_family ht hq₂ (fun U x => lineUnit L (x.face 2)) (fun U x => lineUnit L (x.face 0))
      (hf 2) (hf 0)
    have h₂ : ∀ (U : Scheme.{0}) (y : Sx E 2 U),
        Sec.map ((res _ (tw q 1)).d 0 1) (e U y) = b U (y.face 0) - b U (y.face 1) + b U (y.face 2) := by
      intro U y
      refine sep (loc_mono (loc_and (root_loc (hq₂ U y) (lineUnit L (y.face 2))) (root_loc (hq₂ U y) (lineUnit L (y.face 0)))) ?_)
      rintro V g ⟨⟨v, h⟩, w, h'⟩
      rw [← hf] at h h'
      rw [res_map, res_add, res_sub, he, hb, hb, hb, face_res, face_res, face_res, hw V _ v w h h', hv V _ v h, hv V _ w h',
        hv V _ (v * w) (by rw [mul_pow, h, h', lineUnit_face]), smap_sub, smap_add]
      abel
    have h₃ : ∀ (U : Scheme.{0}) (y : Sx E 3 U),
        e U (y.face 0) - e U (y.face 1) + e U (y.face 2) - e U (y.face 3) = 0 := by
      intro U y
      have hU := hq₂ U (y.face 0)
      refine sep (loc_mono (loc_and (root_loc hU (lineUnit L ((y.face 3).face 2)))
        (loc_and (root_loc hU (lineUnit L ((y.face 0).face 2))) (root_loc hU (lineUnit L ((y.face 0).face 0))))) ?_)
      rintro V g ⟨⟨u, h⟩, ⟨v, h'⟩, w, h''⟩
      rw [← hf, face_res] at h h' h''
      rw [res_sub, res_add, res_sub, he, he, he, he, face_res, face_res, face_res, face_res, res_zero]
      generalize y.res g = z at h h' h'' ⊢
      have e₁ : (z.face 1).face 0 = (z.face 0).face 0 := face_face z _ _ _ _ (by decide)
      have e₂ : (z.face 1).face 2 = (z.face 3).face 1 := face_face z _ _ _ _ (by decide)
      have e₃ : (z.face 2).face 2 = (z.face 3).face 2 := face_face z _ _ _ _ (by decide)
      have e₄ : (z.face 2).face 0 = (z.face 0).face 1 := face_face z _ _ _ _ (by decide)
      have e₅ : (z.face 3).face 0 = (z.face 0).face 2 := face_face z _ _ _ _ (by decide)
      rw [hw V _ v w h' h'', hw V (z.face 1) (u * v) w (by rw [e₂, lineUnit_face, e₅, mul_pow, h, h']) (by rw [e₁, h'']),
        hw V (z.face 2) u (v * w) (by rw [e₃, h]) (by rw [e₄, lineUnit_face, mul_pow, h', h'']),
        hw V (z.face 3) u v h (by rw [e₅, h']), mul_assoc]
      abel
    obtain ⟨α, a₁, a₂⟩ := exists_single (I := res _ (tw q 1)) (n := 2) 1 1 (by simp) b hb
    obtain ⟨β, b₁, b₂⟩ := exists_single (I := res _ (tw q 1)) (n := 2) 2 0 (by simp) e he
    have c₀ : ∀ p s h U x, p ≠ 1 → p ≠ 2 → ev (R := ZMod q) (α + β) p s h U x = 0 := fun p s h U x h₁ h₂ => by
      rw [CupSpec.ev_add, a₂ _ _ _ _ _ h₁, b₂ _ _ _ _ _ h₂, add_zero]
    have c₁ : ∀ h U x, ev (R := ZMod q) (α + β) 1 1 h U x = b U x := fun h U x => by
      rw [CupSpec.ev_add, a₁, b₂ _ _ _ _ _ (by decide), add_zero]
    have c₂ : ∀ h U x, ev (R := ZMod q) (α + β) 2 0 h U x = e U x := fun h U x => by
      rw [CupSpec.ev_add, b₁, a₂ _ _ _ _ _ (by decide), zero_add]
    have hs : (3 : ℤ).negOnePow = -1 := rfl
    refine ⟨Cocycle.mk (α + β) 3 rfl (differential_eq_zero (m := 3) rfl _ (fun U x => ?_) (fun U p s t hs' ht' x => ?_)),
      fun U x => c₀ 0 2 _ U x (by decide) (by decide), fun U x v h => (c₁ _ U x).trans (hv U x v h),
      fun U x v w h h' => (c₂ _ U x).trans (hw U x v w h h')⟩
    · rw [c₀ _ _ _ _ _ (by decide) (by decide), smap_zero]
    · match p with
      | 0 =>
        obtain rfl : s = 1 := by omega
        obtain rfl : t = 2 := by omega
        rw [Finset.sum_eq_zero fun i _ => by rw [c₀ _ _ _ _ _ (by decide) (by decide), smul_zero], smul_zero, add_zero]
        exact (congrArg _ (c₁ _ U x)).trans (hd U x)
      | 1 =>
        obtain rfl : s = 0 := by omega
        obtain rfl : t = 1 := by omega
        rw [Fin.sum_univ_three, c₁, c₁, c₁, c₂, h₂, hs]
        simp
        abel
      | 2 =>
        obtain rfl : t = 0 := by omega
        rw [Fin.sum_univ_four, c₂, c₂, c₂, c₂, c₀ _ _ _ _ _ (by decide) (by decide), smap_zero, zero_add]
        convert smul_zero _
        rw [← h₃ U x]
        norm_num
        abel
      | p + 3 =>
        rw [c₀ _ _ _ _ _ (by omega) (by omega), smap_zero, zero_add,
          Finset.sum_eq_zero fun i _ => by rw [c₀ _ _ _ _ _ (by omega) (by omega), smul_zero], smul_zero]
  intro E L hE
  refine pick_spec (P := fun c : Ht q E 2 1 => ∃ γ : Cocycle _ _ 2, CohomologyClass.mk γ = c ∧
    (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := ZMod q) γ.1 0 2 (by simp) U x = 0) ∧
    (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
      ev (R := ZMod q) γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
    ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
      w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
      ev (R := ZMod q) γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)) ?_
  rcases kumT_cases q with h | h
  · obtain ⟨γ, h₀, h₁, h₂⟩ := exists_cocycle h hE L
    exact ⟨_, γ, rfl, h₀, h₁, fun U x v w hv hw => h₂ U x v w (by rw [hv, sub_zero_one]) (by rw [hw, sub_one_one])⟩
  · refine ⟨_, 0, rfl, fun U x => CupSpec.ev_zero _ _ _ _ _, fun U x v _ => (CupSpec.ev_zero _ _ _ _ _).trans ?_,
      fun U x v w _ _ => (CupSpec.ev_zero _ _ _ _ _).trans ?_⟩
    · rw [h]
      exact (smap_zero _).symm
    · rw [h]
      simp
