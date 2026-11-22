module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CharacterIdealPrincipalEigen
public import ReciprocityTheory.DualLattices.CotangentSurjective
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes

@[expose] public section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_ideal_principal_eigen : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ χ : MulChar F R, (∃ c : R, c ≠ 0 ∧ xIdeal AA.carrier χ = Ideal.span {c}) ∧ ∀ g, g ∈ eig AA.carrier χ ↔ ∃ c ∈ xIdeal AA.carrier χ, g = fun a => algebraMap R C (c * χ a) := by
  intro p _ C _ _ _ v R _ _ hv _ F _ _ _ _ f _ AA _ χ
  obtain ⟨B, hB, hM⟩ := AA.lat
  have key : ∀ d : R, d ∈ xIdeal AA.carrier χ ↔
      (d • fun a => algebraMap R C (χ a)) ∈ AA.carrier := fun d => by
    simp only [xIdeal, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  have smul_char (c : R) :
      (c • fun a => algebraMap R C (χ a)) = fun a => algebraMap R C (c * χ a) := by
    funext a
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
  refine ⟨?_, ?_⟩
  · obtain ⟨c, hc0, hc⟩ := exists_denominator v hv (B⁻¹ *ᵥ fun a => algebraMap R C (χ a))
    refine ⟨c, hc0, ?_⟩
    ext d
    rw [key, hM, mem_span_cols_iff B hB, ← hc d]
    refine forall_congr' fun j => exists_congr fun r => ?_
    rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def]
  · intro g
    constructor
    · rintro ⟨hgM, hg⟩
      have hint : ∀ x, ∃ r : R, algebraMap R C r = g x := AA.le_int hgM
      obtain ⟨r, hr⟩ := hint 1
      have hgf : g = fun a => algebraMap R C (r * χ a) := by
        funext a
        have h := hg a 1
        rw [smul_eq_mul, mul_one] at h
        rw [h, ← hr, map_mul]
        exact mul_comm _ _
      refine ⟨r, ?_, hgf⟩
      rw [key, smul_char, ← hgf]
      exact hgM
    · rintro ⟨c, hc, rfl⟩
      rw [key, smul_char] at hc
      refine ⟨hc, fun a x => ?_⟩
      simp only [smul_eq_mul, map_mul]
      ring
