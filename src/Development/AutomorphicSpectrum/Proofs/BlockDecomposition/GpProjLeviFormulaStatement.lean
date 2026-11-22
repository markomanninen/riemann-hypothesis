module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjLeviFormula
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_levi_formula : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (p : GL (Fin (m + j)) k) (hp : p ∈ parab k (two (stdSum (rfl : m + j = m + j)))) (hp' : levi k (m + j) p ∈ MirabolicParabolic k m j), gpProj k m j ⟨levi k (m + j) p, hp'⟩ = (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ false, levi k j (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ true)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibGP.gpProj_levi | exact GlobalTheory.CompanionTheory.LeibGP.gpProj_levi | (intros; apply GlobalTheory.CompanionTheory.LeibGP.gpProj_levi <;> assumption)
