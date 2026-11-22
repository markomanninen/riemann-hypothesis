module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification

@[expose] public section

noncomputable section

open MeasureTheory
open Formalism.REAL (UJ)
open Formalism.MainNotions.S (IsURepOn UJset allPos)
open GlobalTheory.Dec (HasInfChar IsSqIntIrr UEquiv)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open GlobalTheory.OpTrace (HasTrace repOp)
open GlobalTheory.RealInd (IsIrrAdm groupRep)

namespace GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation

def HasWideGaps {r : ℕ} (lam : Fin r → ℤ) : Prop :=
  StrictAnti lam ∧ ∀ i j : Fin r, (j : ℕ) = i + 1 → (r : ℤ) ≤ lam i - lam j

def IsDiscreteWithInfChar {r : ℕ} (ε : Fin r → Bool) (lam : Fin r → ℤ) {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X)) : Prop :=
  IsSqIntIrr ε D ∧ HasInfChar ε (fun a => (lam a : ℂ)) D

def PseudoCoeffSeparation : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ), HasWideGaps lam →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
      (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X)) (hD : IsDiscreteWithInfChar ε lam D)
      (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (f : UJ ε → ℂ), IsPseudoCoeff (ujMat ε) μ (ujRep hD.1.2.2.1) f →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (π : Matrix (Fin r) (Fin r) ℂ → (V →L[ℂ] V)) (hπ : IsIrrAdm ε π) (c : ℂ),
      HasTrace (repOp (groupRep ε hπ.2.1.1) μ f) c → c ≠ 0 →
        HasInfChar ε (fun a => (lam a : ℂ)) π ∧ (IsURepOn (UJset ε) π → UEquiv ε π D ∧ c = 1)

end GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation

end
