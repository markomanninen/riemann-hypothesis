module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsTestZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesLieAction

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem Zalg_comm_lie : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (z : Module.End ℂ (Sm E a)), z ∈ Zalg E a → ∀ X : Lie E a, z * lie E a X = lie E a X * z :=
  GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie

end GlobalTheory.CompanionTheory.SmoothRep
