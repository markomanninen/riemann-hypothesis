module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HGPClosed
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_mirabolicParabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), IsClosed (MirabolicParabolic k m j : Set (Mir k (m + j))) := by
  first | exact @GlobalTheory.CompanionTheory.MirGP.isClosed_HGP | exact GlobalTheory.CompanionTheory.MirGP.isClosed_HGP | (intros; apply GlobalTheory.CompanionTheory.MirGP.isClosed_HGP <;> assumption)
