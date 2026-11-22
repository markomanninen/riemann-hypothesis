module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalDegreeLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSelfDualClassesRootDiscr
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open Formalism.MainNotions.StandardLattice (stdForm stdLat)
open Formalism.HermitianLatticesTheory (gmap isom genus)

namespace GlobalTheory

namespace StdMassBound

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

noncomputable def matEquiv (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    (Fin n → E) ≃ₗ[E] (Fin n → E) :=
  LinearEquiv.ofLinear (Matrix.mulVecLin γ) (Matrix.mulVecLin γ.conjTranspose)
    (by rw [← Matrix.mulVecLin_mul, h, Matrix.mulVecLin_one])
    (by rw [← Matrix.mulVecLin_mul, mul_eq_one_comm.1 h, Matrix.mulVecLin_one])

theorem matEquiv_mem (γ : Matrix (Fin n) (Fin n) E) (h : γ * γ.conjTranspose = 1) :
    matEquiv γ h ∈ isom (stdForm E n) := by
  intro x y
  change star (γ.mulVec x) ⬝ᵥ (γ.mulVec y) = star x ⬝ᵥ y
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, mul_eq_one_comm.1 h, Matrix.one_mulVec]

theorem diagForm_eq : Examples₂.diagForm (E := E) n (fun _ => false) = stdForm E n := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  change ∑ i, star (x i) * Examples₂.sgn false * y i = ∑ i, star (x i) * y i
  simp [Examples₂.sgn]

variable [NumberField E]

omit [StarRing E] in
theorem stdLat_eq : Examples₂.stdLat (E := E) n = stdLat E n := by
  unfold Examples₂.stdLat stdLat
  congr 2
  funext i
  exact Pi.basisFun_apply E (Fin n) i

omit [StarRing E] in
theorem mem_one_iff (a : E) : a ∈ (1 : Submodule (𝓞 E) E) ↔ IsIntegral ℤ a := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨r, rfl⟩
    exact r.isIntegral_coe
  · intro h
    exact ⟨⟨a, h⟩, rfl⟩

theorem selfDual_of_mem_genus {M : Submodule (𝓞 E) (Fin n → E)} (hM : M ∈ genus (stdForm E n) (stdLat E n))
    (y : Fin n → E) : y ∈ M ↔ ∀ x ∈ M, IsIntegral ℤ (∑ i, star (x i) * y i) := by
  have hsym : (stdForm E n).IsSymm := diagForm_eq (E := E) (n := n) ▸ Examples₂.diagForm_isSymm n _
  obtain ⟨-, -, hinv⟩ := Formalism.HermitianLatticesTheory.genusBasic (𝓞 E) E (Fin n → E) (stdForm E n) hsym
    (Examples₂.star_integral Examples₂.star_isIntegral)
  have h0 : Formalism.HermitianLatticesTheory.IsUnimodular (stdForm E n) (stdLat E n) := by
    rw [← diagForm_eq, ← stdLat_eq]
    exact Examples₂.stdLat_unimod Examples₂.star_isIntegral n _
  have hfg : (stdLat E n).FG := Submodule.fg_span (Set.finite_range _)
  have hu : Formalism.HermitianLatticesTheory.dual (stdForm E n) M = M := ((hinv _ _ hfg hM.1.fg hM.2).1).1 h0
  conv_lhs => rw [← hu]
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, mem_one_iff]
  rfl

end StdMassBound


open StdMassBound in
theorem mass_stdLat_le :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [StarRing E],
    (∀ x : E, star x = IsCMField.complexConj E x) → ∀ n : ℕ,
    Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm E n) (Formalism.MainNotions.StandardLattice.stdLat E n) ≤
      (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^ (3 * Module.finrank ℚ E * n ^ 2) := by
  intro E _ _ _ _ hs n
  have hexists : ∃ R : Finset (Submodule (𝓞 E) (Fin n → E)),
      (R.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG →
        (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (∑ i, IsCMField.complexConj E (x i) * y i)) →
        ∃ L₀ ∈ R, ∃ γ : Matrix (Fin n) (Fin n) E,
          γ * (γ.map (IsCMField.complexConj E)).transpose = 1 ∧
          ∀ x, x ∈ L₀ ↔ γ.mulVec x ∈ L := by
    open RootClassCount ReciprocityTheory.ChartRestriction.G.FD in
    obtain ⟨R, -, h2, h3⟩ := ClassCount.exists_finset_classes (K := E) (r := n) (G := 1)
      {L | L.FG ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (herm 1 y x)}
      (B := 4 * (fdeg E : ℝ) ^ 3 * n ^ 4 * rdE E ^ 2) (by positivity) fun L hL =>
        ⟨by simp, fun x hx => (hL.2 x).1 hx,
          exists_bounded_basis L hL.1 (fun x hx => (hL.2 x).1 hx) fun x hx => (hL.2 x).2 hx⟩
    refine ⟨R, h3.trans ?_, fun L hfg hsd => ?_⟩
    · have h := bound_le (fdeg E) n ClassCount.fdeg_pos (one_le_rootDiscr (E := E))
      rw [← ShortVectors.finrank_eq] at h
      rw [rdE_eq, ← ShortVectors.finrank_eq]
      exact h
    · obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := h2 L ⟨hfg, fun y => by
        simp only [isIntegral_herm_iff]; exact hsd y⟩
      exact ⟨L₀, hL₀, γ, mul_conjTranspose_eq_one _ hγ, hm⟩
  obtain ⟨R, hR, H⟩ := hexists
  refine le_trans ?_ hR
  unfold Formalism.HermitianLatticesTheory.mass
  split_ifs with hex
  swap
  · positivity
  obtain ⟨h1, h2⟩ := hex.choose_spec
  generalize hex.choose = s at h1 h2
  have key : ∀ M ∈ s, ∃ L₀ ∈ R, ∃ g ∈ isom (stdForm E n), gmap g L₀ = M := by
    intro M hM
    obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := H M (h1 M hM).1.fg (fun y => by
      simpa only [hs] using selfDual_of_mem_genus (h1 M hM) y)
    have hγ' : γ * γ.conjTranspose = 1 := by
      rw [← hγ]
      congr 1
      ext i j
      simp [Matrix.conjTranspose_apply, hs]
    refine ⟨L₀, hL₀, matEquiv γ hγ', matEquiv_mem γ hγ', ?_⟩
    ext x
    obtain ⟨x, rfl⟩ := (matEquiv γ hγ').surjective x
    constructor
    · rintro ⟨z, hz, e⟩
      rw [← e]
      exact (hm z).1 hz
    · intro hx
      exact ⟨x, (hm x).2 hx, rfl⟩
  choose! f hf g hg hfg using key
  have hcard : s.card ≤ R.card := by
    refine Finset.card_le_card_of_injOn f (fun M hM => hf M hM) fun M hM N hN e => ?_
    have hM' : M ∈ s := hM
    have hN' : N ∈ s := hN
    refine (h2 M (h1 M hM')).unique ⟨hM', 1, one_mem _, Formalism.HermitianLatticesTheory.genusBasic_gmap_one _⟩
      ⟨hN', g M * (g N)⁻¹, mul_mem (hg M hM') (inv_mem (hg N hN')), ?_⟩
    have e1 : gmap (g N)⁻¹ N = f N := by
      conv_lhs => rw [← hfg N hN']
      rw [hfg N hN']
      have := Formalism.HermitianLatticesTheory.genusBasic_gmap_inv (g N) (f N)
      rwa [hfg N hN'] at this
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, e1, ← e, hfg M hM']
  calc ∑ M ∈ s, ((Nat.card (Formalism.ThetaLiftIndependence.autL (stdForm E n) M) : ℕ) : ℝ)⁻¹ ≤ ∑ M ∈ s, (1 : ℝ) :=
        Finset.sum_le_sum fun M _ => Nat.cast_inv_le_one _
    _ = s.card := by simp
    _ ≤ R.card := by exact_mod_cast hcard

end GlobalTheory
