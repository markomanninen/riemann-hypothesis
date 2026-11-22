module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingMonomialProductsLinearIndependent
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.IndCount
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.JetsPf

@[expose] public section

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingMonomialProducts_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (F : Fin Fl.δ → Frame X.Ψ r → ℂ), (∀ j, DifferentiableOn ℂ (F j) X.dom) → (∀ j j', F j (Fl.xs j') = if j' = j then 1 else 0) → ∀ (T : ℕ) (cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ), (∀ x ∈ X.dom, leadM X Fl.s Fl.w0 F T (T + 1) cc x = 0) → ∀ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) (T + 1), ∀ k, cc α k = 0 := by
  first | exact @GlobalTheory.JetIndepAtPts.leadM_coeff_zero | exact GlobalTheory.JetIndepAtPts.leadM_coeff_zero | (intros; apply GlobalTheory.JetIndepAtPts.leadM_coeff_zero <;> assumption)
