module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne

@[expose] public section

noncomputable section

open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.GelfAct

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry (X : Mat n) (a b : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) a b) (X a b) 0 := by
  have hsmul (t : ℝ) : (t : ℂ) • X = t • X := by ext; simp
  simp only [hsmul]
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let entry : Mat n →L[ℝ] ℂ := (Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap
  exact entry.hasFDerivAt.comp_hasDerivAt 0 h

end GlobalTheory.CompanionTheory.GelfAct

end
