module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacterFormula
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.segment_rep_central_character_formula : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Γ : Segment k) (y : IrrGL (k := k)), IsLSeg Γ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Γ.first t c → Zl.ScalarBy y t (c ^ Γ.len * ((absPow k (Γ.first.1 : ℂ) t : ℂˣ) : ℂ) ^ (Γ.len * (Γ.len - 1) / 2)) := by
  first | exact @GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg | exact GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg | (intros; apply GlobalTheory.CompanionTheory.SegScalar.scalarBy_of_isLSeg <;> assumption)
