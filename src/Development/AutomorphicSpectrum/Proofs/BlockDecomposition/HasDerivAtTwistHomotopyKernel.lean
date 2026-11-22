module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Development.WeilBound.RepresentationTheoryGL.StandardBasisDerivatives.ArchimedeanBasisDerivatives.StBasDeriv

@[expose] public section

noncomputable section

open MvPolynomial Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw

namespace GlobalTheory.CompanionTheory.TwistHomotopy

variable {n : ℕ}

theorem hb_conjTranspose (p : Fin n × Fin n) : (hb p)ᴴ = hb p := by
  unfold hb
  split_ifs with h1 h2
  · simp
  · simp [conjTranspose_smul, conjTranspose_add, add_comm]
  · have e : star (((Real.sqrt 2 : ℂ))⁻¹ * Complex.I) = -(((Real.sqrt 2 : ℂ))⁻¹ * Complex.I) := by
      simp
    rw [conjTranspose_smul, conjTranspose_sub, e]
    simp [neg_smul, smul_sub]
    abel

end GlobalTheory.CompanionTheory.TwistHomotopy
