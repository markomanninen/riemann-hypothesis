module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.YvEqSumMinorsGMat
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.yv_eq_sum_minors_gMat :
    ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
      (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀]
      (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω),
    ∀ r k, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k → ∀ i : idx J₀ n k,
      yv A x₀ ⟨k, i⟩ = ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q)) (coefF A ⟨k, i⟩ I) *
        minorIJ (gMat p q Ω r.1) I (stepCols (p + q) p r.2) := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ r k hk i
  unfold blkF at hk
  split_ifs at hk
  obtain rfl := Option.some.inj hk
  exact BlockEmbeddings.det_fMat_eq A r.1 (stepOf Ψ p q r)
    (BlockEmbeddings.stepOf_fst r) _ (BlockEmbeddings.mem_stepCols_iff r) i
