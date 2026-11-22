module

public import Mathlib
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.SymmetricPowerMatrix
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

@[expose] public section

open Matrix
open Formalism.REAL (inG)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin)
open scoped InnerProductSpace

namespace GlobalTheory.HdSmooth

theorem kFinite_smoothVec : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ v, IsKFin ε σ v → Formalism.L2.Theta.SmoothVec {X | inG ε X} σ v := by
  intro n ε H _ _ _ _ σ hU hI v hv
  have hAnalytic :=
    CompanionTheory.D.gk.HC.kFiniteVectors_analytic_indefiniteUnitary n ε H σ hU hI v hv
  have h := hAnalytic.smoothVec (P := 1) (G := Formalism.REAL.Jm ε) isUnit_one (by simp)
  simpa [inG] using h

end GlobalTheory.HdSmooth
