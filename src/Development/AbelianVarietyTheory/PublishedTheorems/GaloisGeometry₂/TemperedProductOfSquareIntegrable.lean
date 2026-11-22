module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedCoeff

@[expose] public section

noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.Published

def TemperedProductOfSquareIntegrable : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (N : ℕ), 1 ≤ N →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
      (IsTemperedCoeff π ↔ ∃ (h : ℕ) (δ : Fin h → IrrGL (k := k)) (hd : ∑ i, (δ i).1 = N),
        (∀ i, 1 ≤ (δ i).1 ∧ IsSqIntCoeff (δ i).rep) ∧ Nonempty (π.Equiv (prodIrr δ hd)))

namespace TemperedProduct

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]



end TemperedProduct

end GlobalTheory.Published
