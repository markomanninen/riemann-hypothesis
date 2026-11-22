module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PictureMemLevelZeroClass

@[expose] public section

namespace Formalism.FourierDecayAlt.P.PBF

open Finset Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

theorem pairJ_rel {X Y : Type} {w : List C.Letter} (R : X → Y → Prop) (c : ℂ)
    (Ξ1 : (Ix (Fin w.length) → X) → (Ix (Fin w.length) → X) → ℂ)
    (Ξ2 : (Ix (Fin w.length) → Y) → (Ix (Fin w.length) → Y) → ℂ)
    (h : ∀ x x' y y', (∀ e, R (x e) (y e)) → (∀ e, R (x' e) (y' e)) → Ξ1 x x' = c * Ξ2 y y') :
    ∀ (ys : List ℝ) (x : Ix (Fin (KB.plusW ys w).length) → X) (x' : Ix (Fin (KB.minusW ys w).length) → X)
      (y : Ix (Fin (KB.plusW ys w).length) → Y) (y' : Ix (Fin (KB.minusW ys w).length) → Y),
      (∀ e, R (x e) (y e)) → (∀ e, R (x' e) (y' e)) → KB.pairJ Ξ1 ys x x' = c * KB.pairJ Ξ2 ys y y'
  | [], x, x', y, y', hx, hx' => h x x' y y' hx hx'
  | _ :: ys, x, x', y, y', hx, hx' => by
    show KB.pairJ Ξ1 ys _ _ - KB.pairJ Ξ1 ys _ _ = c * (KB.pairJ Ξ2 ys _ _ - KB.pairJ Ξ2 ys _ _)
    have a1 := pairJ_rel R c Ξ1 Ξ2 h ys (fun e => x (Fin.cons 1 e)) (fun e => x' (Fin.cons 0 e))
      (fun e => y (Fin.cons 1 e)) (fun e => y' (Fin.cons 0 e)) (fun e => hx _) (fun e => hx' _)
    have a2 := pairJ_rel R c Ξ1 Ξ2 h ys (fun e => x (Fin.cons 0 e)) (fun e => x' (Fin.cons 1 e))
      (fun e => y (Fin.cons 0 e)) (fun e => y' (Fin.cons 1 e)) (fun e => hx _) (fun e => hx' _)
    exact (congrArg₂ (· - ·) a1 a2).trans (mul_sub _ _ _).symm

theorem prod_real (zs : List ℂ) (h : ∀ z ∈ zs, z.im = 0) : zs.prod.im = 0 ∧ zs.prod.re = (zs.map Complex.re).prod := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hz := h z (by simp)
    obtain ⟨h1, h2⟩ := ih fun z' hz' => h z' (by simp [hz'])
    simp only [List.prod_cons, List.map_cons, Complex.mul_im, Complex.mul_re, hz, h1, mul_zero, zero_mul,
      add_zero, sub_zero, h2]
    exact ⟨trivial, trivial⟩

theorem form_castIx {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    {n m : ℕ} (h : n = m) (U V : Ix (Fin n) → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (fun z => U (z ∘ Fin.cast h)) (fun z => V (z ∘ Fin.cast h)) c = form μ 0 U V c := by
  subst h
  rfl

theorem form_embed {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S'] [DecidableEq S'] (ι : Ix S' → Ix S)
    (hι : Function.Injective ι) (x y : Ix S' → RadSp k r z z' π π') (c : Fin r → ℂ) :
    form μ 0 (Function.extend ι x 0) (Function.extend ι y 0) c = form μ 0 x y c := by
  unfold form
  congr 1
  funext c'
  congr 1
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)), Finset.sum_image (fun a _ b _ h => hι h)]
  · simp only [hι.extend_apply]
  · intro z _ hz
    have : ¬ ∃ a, ι a = z := fun ⟨a, ha⟩ => hz (Finset.mem_image.2 ⟨a, Finset.mem_univ a, ha⟩)
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, pairAt_zero_left]

theorem pairS_embed {V : Type} [AddCommGroup V] [Module ℂ V] {S S' : Type} [Fintype S] [DecidableEq S] [Fintype S']
    [DecidableEq S'] (β : V → V → ℂ) (hβ : ∀ v, β 0 v = 0) (ι : Ix S' → Ix S) (hι : Function.Injective ι)
    (x y : Ix S' → V) : pairS β (Function.extend ι x 0) (Function.extend ι y 0) = pairS β x y := by
  unfold pairS
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image ι)), Finset.sum_image (fun a _ b _ h => hι h)]
  · simp only [hι.extend_apply]
  · intro z _ hz
    have : ¬ ∃ a, ι a = z := fun ⟨a, ha⟩ => hz (Finset.mem_image.2 ⟨a, Finset.mem_univ a, ha⟩)
    rw [Function.extend_apply' _ _ _ this, Pi.zero_apply, hβ]

def ixEmb {m n : ℕ} (h : m ≤ n) (e : Ix (Fin m)) : Ix (Fin n) := fun t => if ht : t.val < m then e ⟨t, ht⟩ else 0

theorem ixEmb_inj {m n : ℕ} (h : m ≤ n) : Function.Injective (ixEmb h) := by
  intro e e' he
  funext t
  have := congrFun he ⟨t.val, by omega⟩
  simpa [ixEmb, t.isLt] using this

theorem bet_neg {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    (v v' : RadSp k r z z' π π') : bet μ (-v) v' = -bet μ v v' := by
  unfold bet
  have := pairLev_smul_left (μ := μ) (i := 0) v v' (fun _ => 1) (-1)
  have e : ((-1 : ℂ) • v) = -v := neg_one_smul ℂ v
  rw [e, neg_one_mul] at this
  exact this

theorem bet_zero {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : MeasureTheory.Measure (Mt k r))
    (v : RadSp k r z z' π π') : bet μ 0 v = 0 := by
  unfold bet; exact pairLev_zero_left v _

section EmbData

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {n : ℕ}
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : MeasureTheory.Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))} {l0 : ℕ}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}

theorem form_zero_eq_position_pairing_of_le (hThm : ThmPOn (S := Fin n) P z z' π π' μ L st K l0) {m : ℕ} (hmn : m ≤ n)
    (Y₁ Y₂ : Ix (Fin m) → RadSp P.k P.r z z' π π') (h₁ : ∀ a, Y₁ a ∈ K 0) (h₂ : ∀ a, Y₂ a ∈ K 0) :
    form μ 0 Y₁ Y₂ 0 = pairS (bet μ) Y₁ Y₂ := by
  have extK : ∀ v : Ix (Fin m) → RadSp P.k P.r z z' π π', (∀ a, v a ∈ K 0) →
      ∀ z, Function.extend (ixEmb hmn) v 0 z ∈ K 0 := by
    intro v hv z
    by_cases hz : ∃ a, ixEmb hmn a = z
    · obtain ⟨a, rfl⟩ := hz
      rw [(ixEmb_inj hmn).extend_apply]; exact hv a
    · rw [Function.extend_apply' _ _ _ hz]; exact (K 0).zero_mem
  have e1 := form_embed μ (ixEmb hmn) (ixEmb_inj hmn) Y₁ Y₂ 0
  have e2 := form_zero_eq_position_pairing hThm (Function.extend (ixEmb hmn) Y₁ 0) (Function.extend (ixEmb hmn) Y₂ 0)
    (extK _ h₁) (extK _ h₂)
  have e3 := pairS_embed (V := RadSp P.k P.r z z' π π') (bet μ) (fun v => bet_zero μ v) (ixEmb hmn) (ixEmb_inj hmn) Y₁ Y₂
  exact e1.symm.trans (e2.trans e3)

end EmbData

theorem final_ineq (Cst : ℝ) (A B P0 Q : ℂ) (qs : List ℂ) (hQ : Q = qs.prod)
    (hqs : ∀ z ∈ qs, 0 < z.re ∧ z.im = 0) (hAi : A.im = 0) (hBi : B.im = 0) (hdk : ‖P0‖ ^ 2 ≤ (A * B / Q).re) :
    ‖(Cst : ℂ) * P0‖ ^ 2 * (qs.map Complex.re).prod ≤ ((Cst : ℂ) * A).re * ((Cst : ℂ) * B).re := by
  obtain ⟨hQi, hQr⟩ := prod_real qs fun z hz => (hqs z hz).2
  have hpos : 0 < (qs.map Complex.re).prod := List.prod_pos fun x hx => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    exact (hqs z hz).1
  have eA : A = (A.re : ℂ) := Complex.ext (by simp) (by simp [hAi])
  have eB : B = (B.re : ℂ) := Complex.ext (by simp) (by simp [hBi])
  have eQ : Q = ((qs.map Complex.re).prod : ℂ) := by
    rw [hQ]; exact Complex.ext (by simp [hQr]) (by simp [hQi])
  have h1 : (A * B / Q).re = A.re * B.re / (qs.map Complex.re).prod := by
    rw [eA, eB, eQ, ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]
    simp
  rw [h1, le_div_iff₀ hpos] at hdk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.re_ofReal_mul, Complex.re_ofReal_mul, mul_pow, sq_abs]
  nlinarith [sq_nonneg Cst]

theorem cast_map_pred {n m : ℕ} (h : n = m) (Q : ∀ k, List (Letter ℂ (Fin k)) → Prop) (u : List (Letter ℂ (Fin n)))
    (hu : Q n u) : Q m (u.map (castL h)) := by
  subst h; rwa [castL_rfl]

theorem Lw_qw (q : ℂ → ℂ) (ys : List ℝ) (w : List C.Letter) :
    ((Lw ys w).map fun l => qw q (Ww ys w) l.pt) = ys.map fun y : ℝ => qw q (D.positionted w) (y : ℂ) := by
  apply List.ext_getElem
  · simp [Lw_length]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_map, Lw_getElem, qw_Ww]

end

end Formalism.FourierDecayAlt.P.PBF

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
