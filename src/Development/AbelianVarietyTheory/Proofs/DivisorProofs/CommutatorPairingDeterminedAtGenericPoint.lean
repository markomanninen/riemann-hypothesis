module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilGeneric

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem weilIs_of_generic : ∀ (O : Type) [CommRing O] [IsDomain O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (N : ℕ), 0 < N → IsUnit (N : O) → ∀ (u v : 𝟙_ (Over (Sp O)) ⟶ A), u ^ N = 1 → v ^ N = 1 → ∀ (c : Oˣ) (k₀ : Type) [Field k₀] (j : O →+* k₀), Function.Injective j → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap j)) ≫ u) (toUnit (Over.mk (spMap j)) ≫ v) (unitOn (Units.map j.toMonoidHom c)) → ∀ (k : Type) [Field k] (ρ : O →+* k), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (toUnit (Over.mk (spMap ρ)) ≫ u) (toUnit (Over.mk (spMap ρ)) ≫ v) (unitOn (Units.map ρ.toMonoidHom c)) := by
  intro O _ _ A _ _ hA P hP h₁ h₂ hamp N hN _ u v hu hv c k₀ _ j hj H k _ ρ
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  let pc {T : Over (Sp O)} (a b : T ⟶ A) : Pic T.left := pull (lift a b).left (cls P hP)
  have hB : ∀ (T : Over (Sp O)) (x x' y : T ⟶ A), pc (x * x') y = pc x y + pc x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp O) A _ hA hD hamp P hP h₁ h₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over (Sp O)) (x y y' : T ⟶ A), pc x (y * y') = pc x y + pc x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp O) A _ hA hD hamp P hP h₁ h₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have pc_pow_left : ∀ {T : Over (Sp O)} (x y : T ⟶ A) (k : ℕ), pc (x ^ k) y = k • pc x y := by
    intro T x y k
    have one : pc (1 : T ⟶ A) y = 0 := by
      have e := hB T 1 1 y
      rwa [_root_.mul_one, left_eq_add] at e
    induction k with
    | zero => rw [pow_zero, one, zero_smul]
    | succ k ih => rw [pow_succ, hB, ih, succ_nsmul]
  have pc_pow_right : ∀ {T : Over (Sp O)} (x y : T ⟶ A) (k : ℕ), pc x (y ^ k) = k • pc x y := by
    intro T x y k
    have one : pc x (1 : T ⟶ A) = 0 := by
      have e := hB' T x 1 1
      rwa [_root_.mul_one, left_eq_add] at e
    induction k with
    | zero => rw [pow_zero, one, zero_smul]
    | succ k ih => rw [pow_succ, hB', ih, succ_nsmul]
  have exists_theta_diag : ∀ {k : ℕ} {T : Over (Sp O)} (x : T ⟶ A), x ^ k = 1 →
      ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) k T, θ.pt = x := by
    intro k T x hx
    have e : ∀ g : T ⊗ A ⟶ A, pull g.left (cls _ hD) = pc g g := fun g => by
      rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    have ha : (fst T A ≫ x) ^ k = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
    have h1 : k • pc (fst T A ≫ x) (fst T A ≫ x) = 0 := by
      rw [← pc_pow_left, ha]
      have e := hB (T ⊗ A) 1 1 (fst T A ≫ x)
      rwa [_root_.mul_one, left_eq_add] at e
    have h2 : k • pc (fst T A ≫ x) (snd T A) = 0 := by
      rw [← pc_pow_left, ha]
      have e := hB (T ⊗ A) 1 1 (snd T A)
      rwa [_root_.mul_one, left_eq_add] at e
    have h3 : k • pc (snd T A) (fst T A ≫ x) = 0 := by
      rw [← pc_pow_right, ha]
      have e := hB' (T ⊗ A) (snd T A) 1 1
      rwa [_root_.mul_one, left_eq_add] at e
    obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB A (P.pull (lift (𝟙 A) (𝟙 A)).left) k x), t.IsGen := by
      refine (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).1 ?_
      rw [cls_linComb hD, Fin.sum_univ_two]
      show (k : ℤ) • pull (snd T A).left _ + (-(k : ℤ)) • pull ((fst T A ≫ x) * snd T A).left _ = 0
      rw [e, e, hB, hB', hB']
      simp only [natCast_zsmul, neg_smul, smul_add, h1, h2, h3]
      abel
    exact ⟨⟨x, t, ht⟩, rfl⟩
  have lifts : ∀ z : 𝟙_ (Over (Sp O)) ⟶ A, z ^ N = 1 → ∀ p : (𝟙_ (Over (Sp O))).left, ∃ V : (𝟙_ (Over (Sp O))).left.Opens,
      p ∈ V ∧ ∃ θ : Out.ThetaGrp A (P.pull (lift (𝟙 A) (𝟙 A)).left) N (Out.overRes V), θ.pt = Out.overResι V ≫ z :=
    fun z hz p => by
      obtain ⟨θ, hθ⟩ := exists_theta_diag (k := N) (Out.overResι ⊤ ≫ z)
        (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
      exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hA hD (lifts u hu) (lifts v hv)
  obtain ⟨w, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 c₀
  have spec : ∀ (F : Type) [Field F] (σ : O →+* F), Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N
      (toUnit (Over.mk (spMap σ)) ≫ u) (toUnit (Over.mk (spMap σ)) ≫ v) (unitOn (Units.map σ.toMonoidHom w)) := by
    intro F _ σ
    have hN' := CommPairing.weilIs_pull hG hA hD (toUnit (Over.mk (spMap σ))) hc₀
    have hl : (toUnit (Over.mk (spMap σ))).left = spMap σ := rfl
    rw [hl, GlobalTheory.Ex.Specialise.map_unitOn] at hN'
    exact hN'
  have e := GlobalTheory.Ex.Specialise.unitOn_bijective.1 (CommutatorPairing.weilIs_unique hG hA hD (spec k₀ j) H)
  have e' : w = c := Units.map_injective hj e
  rw [← e']
  exact spec k ρ

end GlobalTheory.WeilGeneric

end
