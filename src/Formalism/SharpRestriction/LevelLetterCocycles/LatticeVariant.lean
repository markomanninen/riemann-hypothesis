module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.LatticeVariant

open Formalism.MainNotions.IntegralHeckeForms (HkIdx hkO TwOK T3 IsLatIn sIdx specU)
open Formalism.MainNotions.BlochKatoReduction.Gen (psiAt nval SetHyp PsiOk partA partAT partC partD)

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

abbrev LamO (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Type :=
  AddMonoidAlgebra (X.O i) (DelQM D.host (X.l i) Q M)

def ConjCl (Q : Finset (PlE D.host)) : Prop := ∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q

def DelOn (i : X.Tw) (Q : Finset (PlE D.host)) (M : ℕ) : Prop :=
  ∀ (P : PlE D.host) (hP : P ∈ Q) (A' : ValuationSubring N.Om), IsPlaceOver A' P →
    ∃ σ ∈ Ine (F := D.host.E) A', Multiplicative.toAdd (Y.delU i Q M σ) ⟨P, hP⟩ = 1

variable {Y}

variable (Y)

variable (bkP : Formalism.MainNotions.BlochKatoReduction.Gen.BKPh X)






end Formalism.MainNotions.LatticeVariant

end
