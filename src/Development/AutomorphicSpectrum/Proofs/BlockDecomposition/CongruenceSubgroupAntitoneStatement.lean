module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupAntitone
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_antitone : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N m m' : ℕ), m ≤ m' → Zls.Km k N m' ≤ Zls.Km k N m := by
  first | exact @GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone | exact GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone | (intros; apply GlobalTheory.CompanionTheory.CongruenceSubgroups.Km_antitone <;> assumption)
