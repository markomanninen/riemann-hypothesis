module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceOperatorEigenvalueSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieCentralElementTrace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralEigenExponential

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.CentEig

theorem trace_Eop_eq_of_hasInfCharGL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} {τ : E →+* ℂ} {m : Multiset ℂ} (hm : HasInfCharGL V τ m) :
    ∀ φ ∈ V, (∑ i : Fin N, Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hc, hu⟩ := hm
  rcases N with _ | n
  · obtain rfl : m = 0 := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨l, rfl⟩ := Quot.exists_rep m
    refine GlobalTheory.CompanionTheory.CapelliTrace.trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_
    have := hu (v - (n : ℂ) / 2) φ hφ
    rw [cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring] at this
    simpa using this

end GlobalTheory.CompanionTheory.CentEig

end
