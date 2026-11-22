module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.GodementJacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def eMat (k : Type) [Field k] (r t : ℕ) : Matrix (Fin (r + t)) (Fin r) k :=
  Matrix.of fun i j => if (i : ℕ) = j then 1 else 0

end GlobalTheory.GodementJacquet
