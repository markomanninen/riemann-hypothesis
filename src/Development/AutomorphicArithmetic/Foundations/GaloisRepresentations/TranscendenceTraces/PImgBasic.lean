module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCochainEvEqOfNaturalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces

private noncomputable def toOf {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) : A.To (Sq.of p A.u) :=
  ⟨𝟙 _, pullback.lift A.v A.r A.pb.w, Category.id_comp _, pullback.lift_fst _ _ _,
    (pullback.lift_snd _ _ _).trans (Category.comp_id _).symm⟩

private noncomputable def ofTo {Z S V U : Scheme.{0}} (p : Z ⟶ S) (g : V ⟶ U) (u : U ⟶ S) :
    (Sq.of p (g ≫ u)).To (Sq.of p u) :=
  ⟨g, pullback.lift (pullback.fst p (g ≫ u)) (pullback.snd p (g ≫ u) ≫ g)
      (pullback.condition.trans (Category.assoc _ _ _).symm),
    rfl, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

private noncomputable def imgVal {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (τ : Fam p I J) {n : ℤ} (α : Cochain ((chains R').obj (sch.obj Z)) I n) (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s)
    (U : Scheme.{0}) (u : U ⟶ S) : Sec (J.X s) U :=
  (τ.deg s).app (Sq.of p u) (ev (R := R') α k s h (pullback p u) (pullback.fst p u))

end UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.imgBasic_of :
    ImgBasic := by
  intro Z S p R' R _ _ I J τ n
  have ev_def {T : Type} [CommRing T] {E : Spc} {K : Cx T} {j : ℤ}
      (α : Cochain ((chains T).obj E) K j) (k : ℕ) (s : ℤ) (h : -(k : ℤ) + j = s)
      (U : Scheme.{0}) (x : Sx E k U) : ev (R := T) α k s h U x =
        Sec.map ((chainsXIso T E k).inv ≫ α.v _ _ h) (freeGen T _ U x) := rfl
  refine ⟨fun α => ?_, fun m hm α β hαβ => ?_⟩
  · have ev_res (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) {V U : Scheme.{0}}
        (g : V ⟶ U) (x : Sx (sch.obj Z) k U) :
        Sec.res g (ev (R := R') α k s h U x) = ev (R := R') α k s h V (Sx.res g x) := by
      rw [ev_def, CupSpec.map_res, CupSpec.freeGen_res]
      rfl
    have ev_ext (β' β : Cochain ((chains R).obj (sch.obj S)) J n)
        (he : ∀ k s h U x, ev (R := R) β' k s h U x = ev (R := R) β k s h U x) : β' = β := by
      ext i s hs : 1
      by_cases hi : i ≤ 0
      · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = -(k : ℤ) := ⟨(-i).toNat, by omega⟩
        rw [← cancel_epi (chainsXIso R (sch.obj S) k).inv]
        exact CupSpec.free_ext _ _ (fun U x => he k s hs U x)
      · exact (CupSpec.isZero_chains (sch.obj S) i (by omega)).eq_of_src _ _
    have hnat : ∀ (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) (V U : Scheme) (g : V ⟶ U) (u : Sx (sch.obj S) k U),
        Sec.res g (imgVal τ α k s h U u) = imgVal τ α k s h V (Sx.res g u) := by
      intro k s h V U g u
      have e1 : Sec.res g ((τ.deg s).app (Sq.of p u) (ev (R := R') α k s h (pullback p u) (pullback.fst p u))) =
          (τ.deg s).app (Sq.of p (g ≫ u)) (Sec.res (ofTo p g u).k (ev (R := R') α k s h (pullback p u) (pullback.fst p u))) :=
        (τ.deg s).nat (ofTo p g u) _
      have e2 : Sec.res (ofTo p g u).k (ev (R := R') α k s h (pullback p u) (pullback.fst p u)) =
          ev (R := R') α k s h (pullback p (g ≫ u)) (pullback.fst p (g ≫ u)) := by
        refine (ev_res k s h (ofTo p g u).k (pullback.fst p u)).trans ?_
        congr 1
        show (ofTo p g u).k ≫ pullback.fst p u = pullback.fst p (g ≫ u)
        exact pullback.lift_fst _ _ _
      exact e1.trans (congrArg _ e2)
    have hex := exists_cochain_ev_eq_of_natural R (E := sch.obj S) (I := J) (n := n)
      (imgVal τ α) hnat
    obtain ⟨β, hβ⟩ := hex
    have hIm : τ.IsImage α β := by
      intro k s h A
      have e1 : Sec.res (toOf A).g ((τ.deg s).app (Sq.of p A.u) (ev (R := R') α k s h (pullback p A.u) (pullback.fst p A.u))) =
          (τ.deg s).app A (Sec.res (toOf A).k (ev (R := R') α k s h (pullback p A.u) (pullback.fst p A.u))) :=
        (τ.deg s).nat (toOf A) _
      have e2 : Sec.res (toOf A).k (ev (R := R') α k s h (pullback p A.u) (pullback.fst p A.u)) =
          ev (R := R') α k s h A.V A.v := by
        refine (ev_res k s h (toOf A).k (pullback.fst p A.u)).trans ?_
        congr 1
        show (toOf A).k ≫ pullback.fst p A.u = A.v
        exact pullback.lift_fst _ _ _
      exact (hβ k s h A.U A.u).trans (((res_id _).symm.trans e1).trans (congrArg _ e2))
    refine ⟨β, hIm, fun β' h' => ev_ext β' β (fun k s h U u => ?_)⟩
    exact (h' k s h (Sq.of p u)).trans (hIm k s h (Sq.of p u)).symm
  · have ev_delta_zero {T : Type} [CommRing T] {E : Spc} {K : Cx T}
        (γ : Cochain ((chains T).obj E) K n) (U : Scheme.{0}) (x : Sx E 0 U) :
        ev (R := T) (δ n m γ) 0 m (by simp) U x =
          Sec.map (K.d n m) (ev (R := T) γ 0 n (by simp) U x) := by
      rw [ev_def, δ_v n m hm γ _ m (by simp) n 1 (by omega) (by simp),
        (CupSpec.isZero_chains E 1 one_pos).eq_of_tgt (((chains T).obj E).d _ 1) 0,
        zero_comp, smul_zero, add_zero]
      rfl
    have ev_delta_succ {T : Type} [CommRing T] {E : Spc} {K : Cx T}
        (γ : Cochain ((chains T).obj E) K n) (U : Scheme.{0}) (q : ℕ) (s t : ℤ)
        (hs : -((q + 1 : ℕ) : ℤ) + n = s) (ht : -((q + 1 : ℕ) : ℤ) + m = t)
        (x : Sx E (q + 1) U) :
        ev (R := T) (δ n m γ) (q + 1) t ht U x =
          Sec.map (K.d s t) (ev (R := T) γ (q + 1) s hs U x) +
            m.negOnePow • ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
              ev (R := T) γ q t (by omega) U (x.face i) := by
      rw [ev_def, δ_v n m hm γ _ t ht s (-(q : ℤ)) (by omega) (by omega), Preadditive.comp_add,
        Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains T).obj E).d _ _),
        CupSpec.chains_d, Category.assoc, Preadditive.sum_comp]
      refine (map_add (CupSpec.mapHom _ _ (freeGen T _ U x)) _ _).trans ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zsmul, map_sum, Units.smul_def]
      refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
      rw [Preadditive.zsmul_comp, map_zsmul]
      congr 1
      change Sec.map ((chainsXIso T E q).inv ≫ γ.v _ _ _)
        (Sec.map ((free T).map _) (freeGen T _ U x)) = _
      rw [CupSpec.freeGen_map]
      rfl
    intro k s h A
    cases k with
    | zero =>
      have hs : s = m := by simpa using h.symm
      subst hs
      have eβ := ev_delta_zero (E := sch.obj S) β A.U A.u
      have eα := ev_delta_zero (E := sch.obj Z) α A.V A.v
      refine eβ.trans ?_
      refine Eq.trans ?_ (congrArg _ eα.symm)
      refine (congrArg _ (hαβ 0 n (by simp) A)).trans ?_
      exact τ.comm A n s _
    | succ q =>
      have eβ := ev_delta_succ (E := sch.obj S) β A.U q (-((q + 1 : ℕ) : ℤ) + n) s rfl h A.u
      have eα := ev_delta_succ (E := sch.obj Z) α A.V q (-((q + 1 : ℕ) : ℤ) + n) s rfl h A.v
      refine eβ.trans ?_
      refine Eq.trans ?_ (congrArg _ eα.symm)
      rw [map_add (f := _)]
      congr 1
      · exact (congrArg _ (hαβ _ _ rfl A)).trans (τ.comm A _ s _)
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [Units.smul_def, Units.smul_def, map_zsmul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_zsmul]
        congr 1
        exact hαβ q s _ A
