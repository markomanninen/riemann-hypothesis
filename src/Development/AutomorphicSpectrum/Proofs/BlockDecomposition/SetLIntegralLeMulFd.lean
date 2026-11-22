module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedSizeRatGLMul
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting

@[expose] public section

noncomputable section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E
open scoped ENNReal Pointwise
attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace GlobalTheory.CompanionTheory.Growth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem size_facts (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    (∀ C : Set (GA E n), IsCompact C → ∃ r, ∀ g ∈ C, logSize g ≤ r) ∧ (∀ g : GA E n, 0 ≤ logSize g) ∧
      ∃ c : ℝ, 0 ≤ c ∧ ∀ g h : GA E n, logSize (g * h) ≤ logSize g + logSize h + c := by
  obtain ⟨h1, h2, -, c, hc⟩ := GlobalTheory.CompanionTheory.Size.sizeBasic GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin
    GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces E n
  exact ⟨h1, h2, max c 0, le_max_right _ _, fun g h =>
    (hc g h).trans (add_le_add le_rfl (le_max_left _ _))⟩

end GlobalTheory.CompanionTheory.Growth
end
