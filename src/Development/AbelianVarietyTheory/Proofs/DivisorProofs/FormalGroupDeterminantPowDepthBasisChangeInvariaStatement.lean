module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupDeterminantPowDepthBasisChangeInvaria
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.RootStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.FactorialWeightedSumBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.OmBStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatFrame

@[expose] public section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroupDeterminantPowDepth_basis_change_invariant : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C) (g : Matrix (Fin i) (Fin i) C), v g.det = 0 → detDepth G (fun a => ∑ a', g a a' • u a') c = detDepth G u c := by
  first | exact @GlobalTheory.DetDepthBasis.main | exact GlobalTheory.DetDepthBasis.main | (intros; apply GlobalTheory.DetDepthBasis.main <;> assumption)
