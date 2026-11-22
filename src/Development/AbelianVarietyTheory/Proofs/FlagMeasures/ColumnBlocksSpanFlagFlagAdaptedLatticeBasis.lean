module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem eq_top_of_map_lattice_mem {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) {m : ℕ}
    (Λ : Submodule (𝓞 E) (Fin m → E)) (hΛ : Submodule.span E (Λ : Set (Fin m → E)) = ⊤)
    (W : Submodule ℂ (Fin m → ℂ)) (h : ∀ t ∈ Λ, (fun l => φ (t l)) ∈ W) : W = ⊤ := by

  have hall : ∀ x : Fin m → E, (fun l => φ (x l)) ∈ W := by
    intro x
    have hx : x ∈ Submodule.span E (Λ : Set (Fin m → E)) := by rw [hΛ]; trivial
    induction hx using Submodule.span_induction with
    | mem t ht => exact h t ht
    | zero =>
      have e1 : (fun l => φ ((0 : Fin m → E) l)) = 0 := by
        funext l; simp
      rw [e1]; exact W.zero_mem
    | add x y _ _ hx hy =>
      have e1 : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + (fun l => φ (y l)) := by
        funext l; simp
      rw [e1]; exact W.add_mem hx hy
    | smul c x _ hx =>
      have e1 : (fun l => φ ((c • x) l)) = φ c • (fun l => φ (x l)) := by
        funext l; simp
      rw [e1]; exact W.smul_mem _ hx

  have key : ∀ l, (Pi.single l (1 : ℂ) : Fin m → ℂ) ∈ W := by
    intro l
    convert hall (Pi.single l 1) using 1
    funext l'
    by_cases hl : l' = l
    · subst hl; simp
    · simp [hl]
  rw [eq_top_iff]
  intro w _
  have hw : w = ∑ l, w l • (Pi.single l (1 : ℂ) : Fin m → ℂ) := by
    funext l'; simp [Finset.sum_apply, Pi.single_apply]
  rw [hw]
  exact W.sum_mem fun l _ => W.smul_mem _ (key l)

theorem spansFlag_flagAt : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ v, SpansFlag (fun i => (I.P v)⁻¹ * (T i).map (I.φ v)) (flagAt I S v) := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hA v k y
  obtain ⟨-, -, -, hiso, hpair, -, hlam, hS⟩ := hA

  have hspan (i : Fin a) : Submodule.span I.E (Λ i : Set (Fin (j i) → I.E)) = ⊤ := by
    -- The dual frame projects the ambient lattice onto the i-th coordinate block.
    let p := ((T' i)ᴴ * I.J).mulVecLin
    have hJ : I.Jᴴ = I.J := by
      ext r s
      simpa [Formalism.UG.cT, starRingEnd_apply] using congrFun (congrFun I.J_herm r) s
    have hswap (b : Fin a) : (T' i)ᴴ * I.J * T b = ((T b)ᴴ * I.J * T' i)ᴴ := by
      simp [hJ, Matrix.mul_assoc]
    have hpT (x : Fin (j i) → I.E) : p (T i *ᵥ x) = x := by
      simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [hswap, (hpair i).1, Matrix.conjTranspose_one, Matrix.one_mulVec]
    have hple : Submodule.span I.E (lamX I (1, xf) : Set (Fin I.n → I.E)) ≤
        (Submodule.span I.E (Λ i : Set (Fin (j i) → I.E))).comap p := by
      refine Submodule.span_le.2 fun z hz => ?_
      obtain ⟨u, u', z₀, hu, -, -, rfl⟩ := (hlam z).1 hz
      have hsum : p (∑ b, T b *ᵥ u b) = u i := by
        rw [map_sum, Finset.sum_eq_single i, hpT]
        · intro b _ hbi
          simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
          rw [hswap, (hiso b i).2.2 hbi, Matrix.conjTranspose_zero, Matrix.zero_mulVec]
        · simp
      have hsum' : p (∑ b, T' b *ᵥ u' b) = 0 := by
        rw [map_sum]
        refine Finset.sum_eq_zero fun b _ => ?_
        simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
        rw [(hiso i b).2.1, Matrix.zero_mulVec]
      have hp₀ (x : Fin I₀.n → I.E) : p (T₀ *ᵥ x) = 0 := by
        simp only [p, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
        rw [(hpair i).2.2, Matrix.zero_mulVec]
      change p _ ∈ Submodule.span I.E (Λ i : Set (Fin (j i) → I.E))
      rw [map_add, map_add, hsum, hsum', hp₀, add_zero, add_zero]
      exact Submodule.subset_span (hu i)
    rw [(GlobalTheory.PointLattice.lamX_selfDual I (1, xf)).2.2.1] at hple
    refine eq_top_iff.2 fun x _ => ?_
    have hx := hple (Submodule.mem_top (x := T i *ᵥ x))
    rwa [Submodule.mem_comap, hpT] at hx

  have himg : ∀ u : ∀ i, Fin (j i) → I.E,
      ((I.P v)⁻¹ *ᵥ fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) =
        ∑ i, ((I.P v)⁻¹ * (T i).map (I.φ v)) *ᵥ (fun l => I.φ v (u i l)) := by
    intro u
    have e1 : (fun l => I.φ v ((∑ i, T i *ᵥ u i) l)) =
        ∑ i, (T i).map (I.φ v) *ᵥ (fun l => I.φ v (u i l)) := by
      funext l
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Finset.sum_apply, map_sum, RingHom.map_mulVec, Function.comp_def]
    rw [e1, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun i _ => Matrix.mulVec_mulVec _ _ _
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      obtain ⟨u, -, hk, rfl⟩ := (hS k z).1 hz
      refine ⟨fun i l => I.φ v (u i l), fun i hi => ?_, himg u⟩
      funext l
      simp [hk i hi]
    | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', rfl⟩ := hy
      refine ⟨u + u', fun i hi => by simp [hu i hi, hu' i hi], ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_add _ _ _).symm
    | smul c x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨c • u, fun i hi => by simp [hu i hi], ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (Matrix.mulVec_smul _ _ _).symm
  · rintro ⟨u, hu, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hik : i.castSucc < k
    · have htop := eq_top_of_map_lattice_mem (I.φ v) (Λ i) (hspan i)
        ((flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v)))) (by
          intro t ht
          rw [Submodule.mem_comap, Matrix.mulVecLin_apply]
          let w : ∀ i', Fin (j i') → I.E := Pi.single i t
          have hw1 : ∀ i', w i' ∈ Λ i' := by
            intro i'
            by_cases h' : i' = i
            · subst h'; simpa [w] using ht
            · simp [w, Pi.single_eq_of_ne h']
          have hw2 : ∀ i' : Fin a, ¬ i'.castSucc < k → w i' = 0 := by
            intro i' hi'
            have h' : i' ≠ i := by rintro rfl; exact hi' hik
            simp [w, Pi.single_eq_of_ne h']
          have hz : (∑ i', T i' *ᵥ w i') ∈ S k := (hS k _).2 ⟨w, hw1, hw2, rfl⟩
          have hmem := Submodule.subset_span (R := ℂ) (Set.mem_image_of_mem
            (fun y : Fin I.n → I.E => (I.P v)⁻¹ *ᵥ fun l => I.φ v (y l)) hz)
          have hsum := himg w
          rw [hsum, Finset.sum_eq_single i] at hmem
          · simp [w] at hmem
            exact hmem
          · intro i' _ h'
            simp [w, Pi.single_eq_of_ne h']
            exact Matrix.mulVec_zero _
          · simp)
      have : u i ∈ (flagAt I S v k).comap (Matrix.mulVecLin ((I.P v)⁻¹ * (T i).map (I.φ v))) := by
        rw [htop]; trivial
      simpa [Submodule.mem_comap, Matrix.mulVecLin_apply] using this
    · simp [hu i hik]

end GlobalTheory.LeviIso
