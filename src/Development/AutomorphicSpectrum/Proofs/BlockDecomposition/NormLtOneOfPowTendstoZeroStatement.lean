module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormLtOneOfPowTendstoZero
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_lt_one_of_pow_tendsto_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : kˣ), Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0) → nabs k t < 1 := by
  first | exact @GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow | exact GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow | (intros; apply GlobalTheory.CompanionTheory.NabsContract.nabs_lt_one_of_tendsto_pow <;> assumption)
