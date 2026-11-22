module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlkFProperStepInjectiveBlockDiag
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blkF_properStep_injective_blockDiag :
    ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (K₀ : Type),
      (∀ r, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2) ∧
      (∀ r r' k, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k →
        blkF (Ψ := Ψ) (p := p) (q := q) K₀ r' = some k → r = r') ∧
      ∀ τ : Ψ, IsBlockDiag p (gMat p q Ω τ) := by
  intro Ψ _ p q Ω _ K₀
  have stepOf_injective : Function.Injective (stepOf (Ψ := Ψ) (p := p) (q := q)) := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
    have hi := i.2
    have hi' := i'.2
    by_cases h₁ : (i : ℕ) < p <;> by_cases h₂ : (i' : ℕ) < p
    · simp only [stepOf, dite_eq_left h₁, dite_eq_left h₂] at h
      have e₁ : τ = τ' := Sum.inl.inj (congrArg Sigma.fst h)
      have e₂ := congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
      exact Prod.ext e₁ (Fin.ext e₂)
    · simp only [stepOf, dite_eq_left h₁, dite_eq_right h₂] at h
      exact absurd (congrArg Sigma.fst h) (by simp)
    · simp only [stepOf, dite_eq_right h₁, dite_eq_left h₂] at h
      exact absurd (congrArg Sigma.fst h) (by simp)
    · simp only [stepOf, dite_eq_right h₁, dite_eq_right h₂] at h
      have e₁ : τ = τ' := Sum.inr.inj (congrArg Sigma.fst h)
      have e₂ : (i : ℕ) - p = (i' : ℕ) - p :=
        congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
      exact Prod.ext e₁ (Fin.ext (by show (i : ℕ) = (i' : ℕ); omega))
  have fromBlocks_isBlockDiag {R : Type} [CommRing R] (A : Matrix (Fin q) (Fin q) R)
      (B : Matrix (Fin p) (Fin p) R) :
      IsBlockDiag p ((Matrix.fromBlocks A 0 0 B).submatrix
        (blockEquiv p q).symm (blockEquiv p q).symm) := by
    intro a b hab
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases x with x | x <;> rcases y with y | y
    · exfalso
      apply hab
      have hx := x.2
      have hy := y.2
      show ((x : ℕ) < _ ↔ (y : ℕ) < _)
      omega
    · rfl
    · rfl
    · exfalso
      apply hab
      show (q + (x : ℕ) < _ ↔ q + (y : ℕ) < _)
      omega
  refine ⟨?_, ?_, ?_⟩
  · intro r
    unfold blkF
    split_ifs with h <;> simp [h]
  · intro r r' k h h'
    unfold blkF at h h'
    split_ifs at h h'
    apply stepOf_injective
    have e := (Option.some.inj h).trans (Option.some.inj h').symm
    exact Sum.inr.inj e
  · intro τ
    exact fromBlocks_isBlockDiag
      (genU Ω (rk Ψ p q) (.inr τ)) (genU Ω (rk Ψ p q) (.inl τ))
