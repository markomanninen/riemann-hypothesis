module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFirstMinimumLowerBoundNearMax
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.PjFree

namespace GlobalTheory.CuspSecFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mem_SS_of_mem_holSub {Comp : Type} (X : Comp → Data E r) (la : ∀ k, Wt (X k).Ψ r)
    {P : FDSec X} (hP : P ∈ holSub X la) (k : Comp) : P k ∈ (X k).SS (la k) := by
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r (X k) (la k) (la k) 0
  induction hP using Submodule.span_induction with
  | mem P hP => exact hP k
  | zero => exact h0
  | add P Q _ _ h1 h2 => exact hadd _ h1 _ h2
  | smul a P _ h1 => exact hsmul a _ h1

end GlobalTheory.CuspSecFin
