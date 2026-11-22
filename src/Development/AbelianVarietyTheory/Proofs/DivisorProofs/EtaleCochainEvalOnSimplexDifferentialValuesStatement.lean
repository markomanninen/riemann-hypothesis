module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValues
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values :
    ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
      (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
      (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x =
        Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧
      ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s)
        (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
        ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
          m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
  intro R _ E I n m hm α U
  have ev_def {k : ℤ} (β : Cochain ((chains R).obj E) I k) (p : ℕ) (s : ℤ)
      (h : -(p : ℤ) + k = s) (x : Sx E p U) :
      ev β p s h U x = Sec.map ((chainsXIso R E p).inv ≫ β.v _ _ h) (freeGen R _ U x) := rfl
  have hzero (x : Sx E 0 U) :
      ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x) := by
    rw [ev_def, δ_v n m hm α _ m (by simp) n 1 (by omega) (by simp),
      (CupSpec.isZero_chains (R := R) E 1 one_pos).eq_of_tgt (((chains R).obj E).d _ 1) 0,
      zero_comp, smul_zero, add_zero]
    rfl
  have hsucc (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s)
      (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U) :
      ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i) := by
    rw [ev_def, δ_v n m hm α _ t ht s (-(p : ℤ)) (by omega) (by omega), Preadditive.comp_add,
      Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _),
      CupSpec.chains_d, Category.assoc, Preadditive.sum_comp]
    refine (map_add (CupSpec.mapHom _ _ (freeGen R _ U x)) _ _).trans ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zsmul, map_sum, Units.smul_def]
    refine congrArg₂ (· + ·) rfl (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
    rw [Preadditive.zsmul_comp, map_zsmul]
    congr 1
    change Sec.map ((chainsXIso R E p).inv ≫ α.v _ _ _) (Sec.map ((free R).map _) (freeGen R _ U x)) = _
    rw [CupSpec.freeGen_map]
    rfl
  exact ⟨hzero, hsucc⟩
