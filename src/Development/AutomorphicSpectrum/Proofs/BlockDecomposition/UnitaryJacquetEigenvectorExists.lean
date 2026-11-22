module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwGLOfDiag
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetLemmaHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatumStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContractionStatement

@[expose] public section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.EigTorus

theorem eigU_complete :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ∀ y : V, y ∉ jacU ρ →
    (∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ρ k y - y ∈ jacU ρ) →
    ∃ (y' : V) (ξ : GU σ n → ℂ), y' ∉ jacU ρ ∧ (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y' - ξ t • y' ∈ jacU ρ) ∧
      ∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ξ k = 1 :=
  eigU_of GlobalTheory.T.iwahori_unipotent_datum GlobalTheory.T.dominant_unipotent_contraction GlobalTheory.CompanionTheory.KUFactsU.kuFacts (fun G _ _ _ => GlobalTheory.T.jacquet_lemma_holds G)

end GlobalTheory.CompanionTheory.EigTorus
