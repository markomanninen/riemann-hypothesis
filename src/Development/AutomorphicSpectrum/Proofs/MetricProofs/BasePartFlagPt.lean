module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def bvec {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) (b : BM.Rb.X) :
    (Σ k, baseIdx ι M.blk k) → ℂ :=
  fun q => BM.Rb.lift b b q / BM.Rb.lift b b ⟨q.1, (BM.F l).c q.1⟩

def flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : (Σ k, ι k) → ℂ := fun q =>
  if hk : ∀ p, M.blk p ≠ some q.1 then b ⟨⟨q.1, hk⟩, q.2⟩ else
    ∑ I, valAt M.x (F.u q I) b * minorIJ (h (not_forall.1 hk).choose.1) I (stepCols N j (not_forall.1 hk).choose.2)

theorem basePart_flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : basePart M.blk (flagPt M F b h) = b := by
  funext q
  obtain ⟨⟨k, hk⟩, m⟩ := q
  exact dif_pos hk

theorem flagPt_step (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) (m : ι k) :
    flagPt M F b h ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p.1) I (stepCols N j p.2) := by
  have hk : ¬ ∀ p', M.blk p' ≠ some k := fun h' => h' p hp
  simp only [flagPt]
  rw [dite_eq_right hk]
  have key : ∀ p' : Ψ × Fin N, M.blk p' = some k →
      (∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p'.1) I (stepCols N j p'.2))
        = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) b * minorIJ (h p.1) I (stepCols N j p.2) := by
    intro p' hp'
    rw [M.blk_inj _ _ k hp' hp]
  exact key (not_forall.1 hk).choose (not_not.1 (not_forall.1 hk).choose_spec)

theorem exactAt_flagPt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {b : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hb : ∀ k, b ⟨k, F.c k⟩ = 1) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) :
    ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F p (flagPt M F b h) (h p.1) := by
  refine ⟨fun k => by rw [basePart_flagPt]; exact hb k, fun k hp m => ?_⟩
  rw [basePart_flagPt]
  exact flagPt_step M F b h hp m

def wVec (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (t : ℂ) :
    (Σ o : Option K, ι (o.getD k₀)) → ℂ
  | ⟨some k, m⟩ => flagPt M F b h ⟨k, m⟩
  | ⟨none, m⟩ => ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) b *
      minorIJ (h τ * (1 + Matrix.single cb ca t)) I (stepCols N j a)

def plk (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (z : (Σ k, ι k) → ℂ) (p : Ψ × Fin N) : ℂ :=
  (M.blk p).elim 1 fun k => ∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * z ⟨k, m⟩

abbrev CIdx (Ψ : Type) (N j : ℕ) (τ : Ψ) (ca cb : Fin N) : Type := {q : LowIdx Ψ N j // q.1 ≠ (τ, cb, ca)}

def Lc (τ : Ψ) (ca cb : Fin N) (c : CIdx Ψ N j τ ca cb → ℂ) (τ' : Ψ) : Matrix (Fin N) (Fin N) ℂ := fun r s =>
  if h : (s < r ∧ ((r : ℕ) < N - j ↔ (s : ℕ) < N - j)) ∧ (τ', r, s) ≠ (τ, cb, ca) then
    c ⟨⟨(τ', r, s), h.1⟩, h.2⟩ else if r = s then 1 else 0

def Lca (τ : Ψ) (ca cb : Fin N) (c : CIdx Ψ N j τ ca cb → ℂ) (a : ℂ) : Ψ → Matrix (Fin N) (Fin N) ℂ :=
  Function.update (Lc τ ca cb c) τ (Lc τ ca cb c τ * (1 + Matrix.single cb ca a))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
