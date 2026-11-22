module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFirst
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationBijectiveDegreeOneStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionAnalyticOnChartStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ValueConstantOnOrbitStatement

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_chart_first : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a ca cb : Fin N) (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∃ zex : (Fin (d + 1) → ℂ) → (Σ k, ι k) → ℂ, (∀ q', AnalyticOnNhd ℂ (fun u => zex u q') {u : Fin (d + 1) → ℂ | Fin.tail u ∈ Un}) ∧ ∀ u : Fin (d + 1) → ℂ, Fin.tail u ∈ Un → zex u ∈ mcPts (mCoordIdeal y) ∧ ∀ x₀, FA.Re.π x₀ = ΦYn u → SameOrbit (FA.Re.R.lift x₀ x₀) (zex u) ∧ SameOrbit (basePart M.blk (zex u)) (BM.Rb.lift (bp (Fin.tail u)) (bp (Fin.tail u))) ∧ ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) (τ', i) (zex u) (flagAt H τ ca cb (u 0) (Fin.tail u) τ') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.exact_points_holomorphic <;> assumption)
