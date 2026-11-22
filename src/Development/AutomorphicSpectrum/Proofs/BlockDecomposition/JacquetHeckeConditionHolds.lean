module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactFixedVectorProjection
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.HeckeExist

theorem exists_heckeOp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.CH k := by
  intro k _ _ _ _ N J _ hJc V _ _ π hπ g
  obtain ⟨E, hE1, -, hE3, -, -⟩ :=
    GlobalTheory.CompanionTheory.CompactAvg.exists_average (GL (Fin N) k) J hJc V π hπ
  refine ⟨((E ∘ₗ π g ∘ₗ (fixed π J).subtype).codRestrict (fixed π J) (fun v => hE1 _)), ?_⟩
  intro v l hl
  have h := LinearMap.congr_fun (hE3 l hl) (π g (v : V))
  simpa using h.symm

end GlobalTheory.CompanionTheory.HeckeExist
