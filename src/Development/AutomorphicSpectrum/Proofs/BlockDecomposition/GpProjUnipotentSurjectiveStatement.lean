module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotentSurjective
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_unipotent_surjective : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (u : Mir k j), u ∈ MirUin k j → ∃ v : MirabolicParabolic k m j, (v : Mir k (m + j)) ∈ MirUin k (m + j) ∧ gpProj k m j v = (1, u) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip | exact GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip | (intros; apply GlobalTheory.CompanionTheory.BZMir.exists_gpProj_unip <;> assumption)
