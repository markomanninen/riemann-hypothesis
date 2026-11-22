module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct

@[expose] public section

noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.GLFin

section Abstract

variable {Γ K : Type*} [Group Γ] [NormedAddCommGroup K] [InnerProductSpace ℂ K]

end Abstract

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def word (l : List (Lie E a)) : Module.End ℂ (Sm E a) := (l.map (lie E a)).prod

variable (μ : Measure (GA E a)) [μ.IsMulLeftInvariant]

variable {μ} {H : Submodule ℂ (L2 (latticeGL E a) μ)}







end GlobalTheory.GLFin

end
