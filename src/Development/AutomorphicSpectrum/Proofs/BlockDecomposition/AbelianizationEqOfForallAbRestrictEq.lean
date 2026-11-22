module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
public import ReciprocityTheory.ClassFieldTheory.GlobalClassField.AsGabLim

@[expose] public section

open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.GaloisAb

theorem abelianization_eq_of_forall_abRestrict_eq :
    ∀ (K : Type) [Field K] [NumberField K] (a b : Field.absoluteGaloisGroupAbelianization K),
      (∀ (L : IntermediateField K (AlgebraicClosure K)) (h : Neutral.B1.IsFiniteAbelian K L),
        Neutral.B1.abRestrict K L h a = Neutral.B1.abRestrict K L h b) → a = b := by
  intro K _ _ a b hab
  exact ReciprocityTheory.DiscreteGroups.GlobalClassField.abRestrict_ext hab

end GlobalTheory.CompanionTheory.GaloisAb
