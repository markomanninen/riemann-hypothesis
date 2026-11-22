module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.MaIntEmpty
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerSectionBasic

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal

noncomputable section

variable {n d e : ℕ}

def zeroLocus {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {x | ∀ q ∈ J, eval x q = 0}

structure IsAffVariety (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) : Prop where
  isPrime : J.IsPrime
  dim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d



section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
