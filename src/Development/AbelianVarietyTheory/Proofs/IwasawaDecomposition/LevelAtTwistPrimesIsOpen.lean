module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Formalism.LocalToGlobal.Columns.ThetaOpenTwLevQ

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.ChEx


open Classical in
set_option maxHeartbeats 4000000 in
theorem thetaOpen_levQ : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}, L.Ok Ch sel mu cst G m2 → (∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) → ∀ (j : ℕ) (b : L.β j), ThetaOpen (L.levQ j b) := by
  intro X Pr R Ch sel S mu cst L G m2 hL hQg j b P
  have hc : cst.Ok := hL.cst_ok
  let P' : rowSG Pr sel mu := ⟨P.1, Finset.mem_union_right _ P.2⟩
  let h : AutY X R j := L.h j b P'
  have hPg := hQg P.1 P.2
  have hq := ciQ_mem P.1
  have hq0 : ((qOf P.1 : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h0
    exact P.1.ne_bot ((Ideal.absNorm_eq_zero_iff).1 h0)
  obtain ⟨a, ha⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨b', hb⟩ := qth_bound P.1 ((toGLm X.E (R.N j + cOf R j) h⁻¹ : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E)
  obtain ⟨e, he⟩ := qth_exists_e P.1 hq0
  refine ⟨a + b' + e + 1, by omega, fun g hg => ?_⟩
  let r : AutY X R j := twZrExt (c := cOf R j) g.1
  have hr := qth_ext_close (c := cOf R j) P.1 g.1 _ hg
  have hrinv : r⁻¹ = twZrExt (c := cOf R j) (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 := LinearEquiv.ext fun v => rfl
  have hinv {E : Type} [Field E] [NumberField E] [StarRing E]
      (P : HeightOneSpectrum (𝓞 E)) {n N : ℕ} (g : ↥(GLint E n P))
      (hg : lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n)) :
      lqPrinc P N ((g⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := by
    unfold lqPrinc at hg ⊢
    intro i j
    set A := LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hA
    set B := LinearMap.toMatrix'
      ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) with hB
    have hBA : B * A = 1 := by
      rw [hA, hB, ← LinearMap.toMatrix'_comp]
      have hc : ((((g⁻¹ : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n).comp
          ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) = LinearMap.id := by
        refine LinearMap.ext fun x => ?_
        have hx : ((((g⁻¹ * g : GLint E n P)) : Sp E n ≃ₗ[E] Sp E n)) x = x := by
          rw [inv_mul_cancel]
          rfl
        exact hx
      rw [hc, LinearMap.toMatrix'_id]
    have hBle : ∀ a k, P.valuation E (B a k) ≤ 1 := by
      intro a k
      rw [hB, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
      have hs : (Pi.single k (1 : E) : Sp E n) ∈ stdAt E n P := by
        show _ ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n)
        rw [mem_localization_standardLattice]
        intro t
        rw [qth_intAt_iff]
        by_cases h : t = k
        · subst h
          simp
        · simp [Pi.single_apply, h]
      have hmem : ((g⁻¹ : GLint E n P) : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (stdAt E n P) :=
        (g⁻¹ : GLint E n P).2
      have h2 := (hmem _).2 hs
      have h3 := (mem_localization_standardLattice P _).1 h2 a
      rw [qth_intAt_iff] at h3
      exact h3
    have hBm : B - 1 = -(B * (A - 1)) := by
      rw [Matrix.mul_sub, hBA, Matrix.mul_one, neg_sub]
    rw [hBm, Matrix.neg_apply, Valuation.map_neg, Matrix.mul_apply]
    refine Valuation.map_sum_le _ (fun k _ => ?_)
    rw [map_mul]
    calc _ ≤ 1 * P.valuation E ((A - 1) k j) := mul_le_mul' (hBle i k) le_rfl
      _ ≤ _ := by rw [one_mul]; exact hg k j
  
  have hr' := qth_ext_close (c := cOf R j) P.1 (g⁻¹ : ↥(GLint X.E (R.N j) P.1)).1 _ (hinv P.1 g hg)
  have hy : QClose P.1 (qOf P.1) (h⁻¹ * r * h) := qth_conj_close P.1 (qOf P.1) h r a b' _ e ha hb hr he (by omega)
  have hy' : QClose P.1 (qOf P.1) (h⁻¹ * r * h)⁻¹ := by
    have e3 : (h⁻¹ * r * h)⁻¹ = h⁻¹ * r⁻¹ * h := by simp only [_root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [e3, hrinv]
    exact qth_conj_close P.1 (qOf P.1) h _ a b' _ e ha hb hr' he (by omega)
  have hJ : h⁻¹ * r * h ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1 := by
    rw [twJat_Q cst.sharp j hPg]
    exact qth_mem_JQ P.1 (qOf P.1) hq0 (R.k + j) _ hy hy'
  have hC : r ∈ Loc.Cbe (Jat (Pr := Pr) (R := R) cst.sharp j P.1) h := by
    refine ⟨zeroExtension_mem_R1 g.1, ?_⟩
    show (MulAut.conj h⁻¹) r ∈ Jat (Pr := Pr) (R := R) cst.sharp j P.1
    simpa [MulAut.conj_apply] using hJ
  have hmem : g.1 ∈ prCat (Pr := Pr) cst.sharp j P.1 h := ⟨r, hC, twZrExt_inX g.1⟩
  have hH : g ∈ (L.levQ j b P).H := by
    rw [hL.grpQ j b P]
    exact Subgroup.mem_subgroupOf.2 hmem
  refine ⟨hH, ?_⟩
  apply Units.ext
  rw [hL.chrQ j b P ⟨g, hH⟩ r hC (fun x => twZrExt_inX g.1 x)]
  have hstd : r ∈ stabL X.E (R.N j + cOf R j) (stdAt X.E (R.N j + cOf R j) P.1) :=
    twZrExt_stab P.1 _ (fun v => ciMem_stdAt P.1 v) g.2
  have hint : IntAt P.1 (Loc.n1Arg r) := by
    unfold Loc.n1Arg
    refine ciIntAt_sum _ _ fun i _ => ?_
    have hv : r (Loc.eN X.E (R.N j + cOf R j) (R.N j + i + 1)) ∈ stdAt X.E (R.N j + cOf R j) P.1 :=
      (hstd _).2 (twZr_eN_mem P.1 _ _)
    rw [ciMem_stdAt] at hv
    unfold Loc.atN
    split_ifs
    · exact hv _
    · exact ciIntAt_zero
  unfold chiInv
  rw [hc.psi_int P' _ hint, inv_one, one_mul]
  unfold lamRow
  rw [if_neg hPg]
  have hlam {P : HeightOneSpectrum (𝓞 X.E)} (hq : ((qOf P : ℕ) : 𝓞 X.E) ∈ P.asIdeal) (hq0 : ((qOf P : ℕ) : X.E) ≠ 0) {j : ℕ}
      (ξ : (𝓞 X.E ⧸ P.asIdeal)ˣ →* X.Kˣ) (y : AutY X R j) (hy : QClose P (qOf P) y) :
      LocE.lamQB ξ (R.k + j) (R.N j) (y : Sp X.E (R.N j + cOf R j) →ₗ[X.E] Sp X.E (R.N j + cOf R j)) = 1 := by
    classical
    unfold LocE.lamQB
    set D : Matrix (Fin (R.N j - (R.k + j))) (Fin (R.N j - (R.k + j))) X.E := Matrix.of fun s t : Fin (R.N j - (R.k + j)) =>
      Loc.atN ((y : Sp X.E (R.N j + cOf R j) →ₗ[X.E] Sp X.E (R.N j + cOf R j)) (Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1))) (R.k + j + s.1) with hD
    have hent : ∀ s t : Fin (R.N j - (R.k + j)), IntAt P (D s t) ∧ redP P (D s t) = (1 : Matrix _ _ (𝓞 X.E ⧸ P.asIdeal)) s t := by
      intro s t
      have hs : R.k + j + s.1 < R.N j + cOf R j := by have := s.2; omega
      have ht : R.k + j + t.1 < R.N j + cOf R j := by have := t.2; omega
      have e1 : Loc.eN X.E (R.N j + cOf R j) (R.k + j + t.1) = Pi.single ⟨R.k + j + t.1, ht⟩ 1 := by
        funext l
        unfold Loc.eN
        rw [Pi.single_apply]
        congr 1
        apply propext
        constructor
        · intro h; exact Fin.ext h
        · intro h; rw [h]
      have e2 : D s t = ((toGLm X.E (R.N j + cOf R j) y : GL (Fin (R.N j + cOf R j)) X.E) : Matrix (Fin (R.N j + cOf R j)) (Fin (R.N j + cOf R j)) X.E) ⟨R.k + j + s.1, hs⟩ ⟨R.k + j + t.1, ht⟩ := by
        rw [qsp_toGLm_apply, hD, Matrix.of_apply, e1]
        unfold Loc.atN
        rw [dite_eq_left hs]
        rfl
      obtain ⟨h1, h2⟩ := qth_red_entry P (qOf P) hq0 hq hy ⟨R.k + j + s.1, hs⟩ ⟨R.k + j + t.1, ht⟩
      rw [e2]
      refine ⟨h1, ?_⟩
      rw [h2, Matrix.one_apply, Matrix.one_apply]
      by_cases hst : s = t
      · rw [if_pos (Fin.ext (by simp [hst])), if_pos hst, redP_one]
      · rw [if_neg (fun h => hst (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))), if_neg hst, redP_zero]
    have hdet : redP P D.det = 1 := by
      rw [redP_det D fun s t => (hent s t).1]
      have : D.map (redP P) = 1 := Matrix.ext fun s t => (hent s t).2
      rw [this, Matrix.det_one]
    unfold LocE.unitV
    have hu : IsUnit (redP P D.det) := by rw [hdet]; exact isUnit_one
    rw [dite_eq_left hu]
    have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
    rw [this, map_one, Units.val_one, inv_one]
  exact hlam hq hq0 _ _ hy

end GlobalTheory.Mem.Col2.ChEx
