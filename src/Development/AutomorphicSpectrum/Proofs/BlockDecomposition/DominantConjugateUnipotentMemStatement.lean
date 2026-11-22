module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantConjugateUnipotentMem
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPermWOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwUIff

@[expose] public section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_conjugate_unipotent_mem : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (t u : GU σ n), IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) → u ∈ IwU σ n → IsUnipU u → ∀ k : ℕ, t ^ k * u * (t ^ k)⁻¹ ∈ KU σ n := by
  first | exact @GlobalTheory.CompanionTheory.SatPow.conj_unip_mem_KU | exact GlobalTheory.CompanionTheory.SatPow.conj_unip_mem_KU | (intros; apply GlobalTheory.CompanionTheory.SatPow.conj_unip_mem_KU <;> assumption)
