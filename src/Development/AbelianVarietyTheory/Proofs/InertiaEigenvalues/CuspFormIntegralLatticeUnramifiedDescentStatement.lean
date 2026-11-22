module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormIntegralLatticeUnramifiedDescent
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.MulCMemSec
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
open GlobalTheory.SupDescent in
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 100000 in
theorem _root_.GlobalTheory.T.cuspForm_integral_lattice_unramified_descent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → l.GoodAt p → ∀ (c' : Coeff l) (hle : c.F ≤ c'.F) (la' : HeightOneSpectrum (𝓞 c'.F)), (∀ x : c.F, vLa la' (incF c c' hle x) = vLa la x) → CuspBC hle U → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → FiniteDimensional c.F (cusp Xo c U a n) → ∀ f' ∈ cusp Xo c' (unfBC hle U) a n, BddAll Xo c' la' 1 f' → ∃ (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), (∀ i, la'.valuation c'.F (as i) ≤ 1) ∧ (∀ i, fs i ∈ supSet Xo c la (cusp Xo c U a n)) ∧ IsBC hle f' as fs := by
  intro E _ _ _ H Dw l Xo c r U hU la p hp hpl hgood c' hle la' hv hBC a n hD _ f' hf' hb
  obtain ⟨m, as, fs, hfs, hIs⟩ := hBC a n f' hf'
  choose κ hκ0 hκ using fun i => GlobalTheory.T.cuspidal_section_bounded_nonzero_multiple E H Dw l Xo c r U hU la p hp hpl hgood a n (fs i) hD (hfs i)
  let : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  have := liesOver (K := c.F) (K' := c'.F) hv
  obtain ⟨d, b, hb1, hb2⟩ := exists_residue_basis (la := la) (la' := la')
  choose x ρ hρ hx using fun i => exists_approx (K := c.F) (K' := c'.F) hv hb2 (as i) (hκ0 i)
  let F : Fin d → Rul Xo c := fun j => ∑ i, x i j • fs i
  have hF : ∀ j, F j ∈ cusp Xo c U a n := fun j => Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hfs i)
  have hG : ∀ i, κ i • fs i ∈ supSet Xo c la (cusp Xo c U a n) := fun i =>
    ⟨Submodule.smul_mem _ _ (hfs i), (GlobalTheory.GoodPtsModel.bddAll_iff_smul _ _).1 (hκ i)⟩
  have key : ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] (h : AlgOver c c' hle S) (y : FrPt Xo c' S),
      evR Xo c' f' y = ∑ j, algebraMap c'.F S (b j) * evR Xo c (F j) (y.res hle h) +
        ∑ i, algebraMap c'.F S (ρ i) * evR Xo c (κ i • fs i) (y.res hle h) := by
    intro S _ _ _ h y
    have h' : ∀ t : c.F, algebraMap c'.F S (algebraMap c.F c'.F t) = algebraMap c.F S t := h
    have hs : ∀ i, evR Xo c (κ i • fs i) (y.res hle h) = algebraMap c.F S (κ i) * evR Xo c (fs i) (y.res hle h) :=
      fun i => evalAt_smul _ _ _ _ _
    rw [hIs S h y]
    simp only [F, evR_sum, hs, Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx i]
    simp only [map_add (f := _), map_sum, map_mul, h', add_mul, Finset.sum_mul, mul_assoc]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  refine ⟨d + m, Fin.append (fun j => (b j : c'.F)) ρ, Fin.append F fun i => κ i • fs i, fun i => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact la'.valuation_le_one (b j)
    · rw [Fin.append_right]; exact hρ j
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    swap
    · rw [Fin.append_right]; exact hG j
    rw [Fin.append_left]
    refine ⟨hF j, fun T io e ho y hy => ?_⟩
    rw [map_one, one_mul]
    refine inV_of_forall_emb (K := c.F) (K' := c'.F) hb1 hy ho (fun j => evI y (F j)) ?_ j
    intro T' i e' σ e'' he' hi hT' hσ ho'
    obtain ⟨y₁, φ, hφ, hmap⟩ := GlobalTheory.IntFrBaseChange.exists_intFr_baseChange E H Dw l Xo c T T' io y i e' he' hi
    obtain ⟨y₂, hy₂⟩ := exists_intFr_ext hle (io := i.comp io) σ hσ y₁
    have hi' : ∀ t : T.Fr, vV T'.V (i t) = (e' : ℤ) * vV T.V t := fun t => by
      by_cases h : t = 0
      · subst h; simp [vV]
      · exact hi t h
    have h1 := hb T' σ e'' ho' y₂ hT'
    rw [map_one, one_mul] at h1
    have h2 : InV T' (∑ k, σ (ρ k) * evI y₁ (κ k • fs k)) := Subring.sum_mem _ fun k _ => by
      have h3 := (hG k).2 T' _ _ (ho.bc i he' hi') y₁ hT'
      rw [map_one, one_mul] at h3
      exact Subring.mul_mem _ ((GlobalTheory.GoodPtsModel.inV_iff_val T' _).2
        ((val_le_one_iff ho' _).2 (hρ k))) h3
    have h4 : ∀ j, i (evI y (F j)) = evI y₁ (F j) := fun j => by
      let := io.toAlgebra
      let := (i.comp io).toAlgebra
      exact (DFunLike.congr_fun hφ _).symm.trans
        (GlobalTheory.FlagTan.evR_frMap (cusp_le_sec Xo c U a n (hF j)).1 hmap).symm
    have h5 : evI y₂ f' = ∑ j, σ (b j) * evI y₁ (F j) + ∑ k, σ (ρ k) * evI y₁ (κ k • fs k) := by
      let := (i.comp io).toAlgebra
      let := σ.toAlgebra
      have := key T'.Fr hσ y₂.1
      rw [hy₂] at this
      exact this
    simp only [h4]
    rw [eq_sub_of_add_eq h5.symm]
    exact Subring.sub_mem _ h1 h2
  · intro S _ _ _ h y
    rw [key S h y, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
